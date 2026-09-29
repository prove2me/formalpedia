-- Prove2me | solution 1 for BanditAlgorithm.bandit_divergence_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-20T17:19:05.079401+00:00
-- url     : https://prove2.me/submissions/562e3d5f-05ad-4d66-b7da-32a357042865

import Theorems.Thm_BanditAlgorithm_bandit_divergence_one_step
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

private theorem armPullCount_snoc_kl {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add]
  simp only [armPullCount]
  have hset (g : BanditHistory k n) :
      ({t | (g t).1 = i}.toFinset.card : ℝ) =
        ∑ t, if (g t).1 = i then 1 else 0 := by
    have hs : {t | (g t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (g t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (g t).1 = i) Finset.univ).symm
  rw [hset]
  have hsnoc :
      (({t | (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset.card : ℕ) : ℝ) =
        ∑ t, if (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i then 1 else 0 := by
    have hs : {t | (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset =
        Finset.univ.filter
          (fun t ↦ (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin (n + 1) ↦
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i)
        Finset.univ).symm
  rw [hsnoc, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem measurable_armPullCount_kl {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  have ha : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage ha)
    measurable_const measurable_const

private theorem armPullCount_cast_le_length_kl {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) : (armPullCount i h : ℝ) ≤ n := by
  rw [show (armPullCount i h : ℝ) =
      ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm]
  calc
    (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤ ∑ _t : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      split <;> norm_num
    _ = n := by simp

private theorem integrable_armPullCount_kl {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_armPullCount_kl i).aemeasurable
  · filter_upwards [] with h
    exact ⟨by positivity, armPullCount_cast_le_length_kl i h⟩

private theorem measurable_selection_probability_kl {k n : ℕ}
    (π : BanditPolicy k) (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (π.select n h).real {i}) := by
  exact (Kernel.measurable_coe (π.select n) (measurableSet_singleton i)).ennreal_toReal

private theorem selection_probability_mem_Icc_kl {k n : ℕ}
    (π : BanditPolicy k) (h : BanditHistory k n) (i : Fin k) :
    (π.select n h).real {i} ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · calc
      (π.select n h).real {i} ≤ (π.select n h).real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp

private theorem integral_step_arm_indicator_kl {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k)
    (h : BanditHistory k n) (i : Fin k) :
    ∫ z, (if z.1 = i then (1 : ℝ) else 0) ∂banditStepKernel ν π n h =
      (π.select n h).real {i} := by
  rw [banditStepKernel]
  rw [ProbabilityTheory.integral_compProd]
  · simp only [Kernel.comap_apply, banditRewardKernel, Kernel.ofFunOfCountable]
    have hin (x : Fin k) :
        (∫ _y : ℝ, if x = i then (1 : ℝ) else 0 ∂ν.P x) =
          if x = i then 1 else 0 := by
      by_cases hxi : x = i <;> simp [hxi]
    calc
      (∫ x, ∫ _y : ℝ, if x = i then (1 : ℝ) else 0 ∂ν.P x ∂(π.select n) h) =
          ∫ x, if x = i then (1 : ℝ) else 0 ∂(π.select n) h :=
        integral_congr_ae (Filter.Eventually.of_forall hin)
      _ = (π.select n h).real {i} := by
        calc
          (∫ x, if x = i then (1 : ℝ) else 0 ∂(π.select n) h) =
              ∫ x, ({i} : Set (Fin k)).indicator (1 : Fin k → ℝ) x ∂(π.select n) h := by
            apply integral_congr_ae
            filter_upwards [] with x
            by_cases hxi : x = i
            · subst x
              simp only [if_pos, Set.indicator_of_mem (Set.mem_singleton i), Pi.one_apply]
            · have hnmem : x ∉ ({i} : Set (Fin k)) := by
                simpa [Set.mem_singleton_iff] using hxi
              rw [Set.indicator_of_notMem hnmem]
              simp [hxi]
          _ = (π.select n h).real {i} :=
            integral_indicator_one (measurableSet_singleton i)
  · apply Integrable.of_mem_Icc 0 1
    · exact (Measurable.ite
        ((measurableSet_singleton i).preimage measurable_fst)
        measurable_const measurable_const).aemeasurable
    · filter_upwards [] with z
      split <;> simp

private theorem integral_armPullCount_succ_kl {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π (n + 1) =
      (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) +
        ∫ h, (π.select n h).real {i} ∂banditMeasure ν π n := by
  let μ := banditMeasure ν π n
  let κ := banditStepKernel ν π n
  let snoc : BanditHistory k n × (Fin k × ℝ) → BanditHistory k (n + 1) :=
    fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
  have hsnoc : Measurable snoc := measurable_banditHistorySnoc
  have hcomp : Integrable
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        (armPullCount i (snoc p) : ℝ)) (μ.compProd κ) := by
    apply Integrable.of_mem_Icc 0 (n + 1)
    · exact ((measurable_armPullCount_kl i).comp hsnoc).aemeasurable
    · filter_upwards [] with p
      constructor
      · positivity
      · simpa only [Nat.cast_add, Nat.cast_one] using
          (armPullCount_cast_le_length_kl i (snoc p))
  rw [banditMeasure,
    integral_map hsnoc.aemeasurable
      (measurable_armPullCount_kl i).aestronglyMeasurable]
  change (∫ p, (armPullCount i (snoc p) : ℝ) ∂(μ.compProd κ)) = _
  rw [Measure.integral_compProd hcomp]
  have hsel_int : Integrable
      (fun h : BanditHistory k n ↦ (π.select n h).real {i}) μ := by
    apply Integrable.of_mem_Icc 0 1
    · exact (measurable_selection_probability_kl π i).aemeasurable
    · filter_upwards [] with h
      exact selection_probability_mem_Icc_kl π h i
  rw [← integral_add (integrable_armPullCount_kl ν π i) hsel_int]
  apply integral_congr_ae
  filter_upwards [] with h
  rw [show (∫ z, (armPullCount i (snoc (h, z)) : ℝ) ∂κ h) =
      ∫ z, ((armPullCount i h : ℝ) + if z.1 = i then 1 else 0) ∂κ h by
    apply integral_congr_ae
    filter_upwards [] with z
    rw [armPullCount_snoc_kl, Nat.cast_add]
    split <;> simp]
  rw [integral_add]
  · simp [κ, integral_step_arm_indicator_kl]
  · exact integrable_const _
  · apply Integrable.of_mem_Icc 0 1
    · exact (Measurable.ite
        ((measurableSet_singleton i).preimage measurable_fst)
        measurable_const measurable_const).aemeasurable
    · filter_upwards [] with z
      split <;> simp

end BanditAlgorithm

theorem solution {k : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit k)
    (hKL : ∀ i, klDiv (ν.P i) (ν'.P i) ≠ ⊤)
    (π : BanditAlgorithm.BanditPolicy k) (n : ℕ) :
    klDiv (BanditAlgorithm.banditMeasure ν π n) (BanditAlgorithm.banditMeasure ν' π n) =
      ∑ i, ENNReal.ofReal
        (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂BanditAlgorithm.banditMeasure ν π n) *
        klDiv (ν.P i) (ν'.P i) := by
  induction n with
  | zero =>
      simp [BanditAlgorithm.banditMeasure, BanditAlgorithm.armPullCount]
  | succ n ih =>
      rw [BanditAlgorithm.bandit_divergence_one_step ν ν' hKL π]
      rw [ih]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [BanditAlgorithm.integral_armPullCount_succ_kl]
      rw [ENNReal.ofReal_add]
      · rw [add_mul]
      · positivity
      · positivity
