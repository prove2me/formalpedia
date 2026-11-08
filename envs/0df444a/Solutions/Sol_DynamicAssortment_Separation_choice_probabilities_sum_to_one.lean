-- Prove2me | solution 1 for DynamicAssortment.Separation.choice_probabilities_sum_to_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:28:23.041345+00:00
-- url     : https://prove2.me/submissions/23cf988f-dacc-4490-a873-b3bf61290d23

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel

open MeasureTheory Set Filter Topology DynamicAssortment.Separation

private theorem ibp_Iic (a b : ℝ → ℝ) (ha : Integrable a) (hb : Integrable b) (x : ℝ) :
    (∫ s in Iic x, a s * (∫ t in Iic s, b t)) + ∫ t in Iic x, (∫ s in Iic t, a s) * b t =
      (∫ s in Iic x, a s) * (∫ t in Iic x, b t) := by
  set Φ : ℝ × ℝ → ℝ := fun p => a p.1 * b p.2 with hΦdef
  have hΦ : Integrable Φ (volume.prod volume) := ha.mul_prod hb
  set D1 : Set (ℝ × ℝ) := {p | p.1 ≤ x ∧ p.2 < p.1} with hD1def
  set D2 : Set (ℝ × ℝ) := {p | p.2 ≤ x ∧ p.1 ≤ p.2} with hD2def
  have hD1 : MeasurableSet D1 :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hD2 : MeasurableSet D2 :=
    (measurableSet_le measurable_snd measurable_const).inter
      (measurableSet_le measurable_fst measurable_snd)
  have c1 : ∫ s in Iic x, a s * (∫ t in Iic s, b t) =
      ∫ p, D1.indicator Φ p ∂(volume.prod volume) := by
    rw [integral_prod _ (hΦ.indicator hD1), ← integral_indicator measurableSet_Iic]
    congr 1; funext s
    by_cases hs : s ≤ x
    · have : (fun t => D1.indicator Φ (s, t)) = fun t => a s * (Iio s).indicator b t := by
        funext t
        by_cases ht : t < s
        · simp [D1, Set.indicator, hs, ht, Φ]
        · simp [D1, Set.indicator, ht, Φ]
      rw [this, integral_const_mul, integral_indicator measurableSet_Iio,
        Set.indicator_of_mem (show s ∈ Iic x from hs), integral_Iic_eq_integral_Iio]
    · rw [Set.indicator_of_notMem (show s ∉ Iic x from hs)]
      have : (fun t => D1.indicator Φ (s, t)) = fun _ => 0 := by
        funext t; simp [D1, Set.indicator, hs]
      rw [this, integral_zero]
  have c2 : ∫ t in Iic x, (∫ s in Iic t, a s) * b t =
      ∫ p, D2.indicator Φ p ∂(volume.prod volume) := by
    rw [integral_prod_symm _ (hΦ.indicator hD2), ← integral_indicator measurableSet_Iic]
    congr 1; funext t
    by_cases ht : t ≤ x
    · have : (fun s => D2.indicator Φ (s, t)) = fun s => (Iic t).indicator a s * b t := by
        funext s
        by_cases hst : s ≤ t
        · simp [D2, Set.indicator, ht, hst, Φ]
        · simp [D2, Set.indicator, hst, Φ]
      rw [this, integral_mul_const, integral_indicator measurableSet_Iic,
        Set.indicator_of_mem (show t ∈ Iic x from ht)]
    · rw [Set.indicator_of_notMem (show t ∉ Iic x from ht)]
      have : (fun s => D2.indicator Φ (s, t)) = fun _ => 0 := by
        funext s; simp [D2, Set.indicator, ht]
      rw [this, integral_zero]
  rw [c1, c2, ← integral_add (hΦ.indicator hD1) (hΦ.indicator hD2)]
  have : (fun p => D1.indicator Φ p + D2.indicator Φ p) = (Iic x ×ˢ Iic x).indicator Φ := by
    funext p
    obtain ⟨s, t⟩ := p
    by_cases hs : s ≤ x <;> by_cases ht : t ≤ x <;> by_cases hts : t < s <;>
      simp [D1, D2, Set.indicator, hs, ht, hts] <;> linarith
  rw [this, integral_indicator (measurableSet_Iic.prod measurableSet_Iic)]
  exact setIntegral_prod_mul a b (Iic x) (Iic x)

section
variable {f : ℝ → ℝ} (hf : IsNoiseDensity f)
include hf

private theorem F_nonneg (x : ℝ) : 0 ≤ noiseCDF f x :=
  setIntegral_nonneg measurableSet_Iic (fun y _ => (hf.pos y).le)

private theorem F_le_one (x : ℝ) : noiseCDF f x ≤ 1 := by
  rw [← hf.integral_eq_one]
  exact setIntegral_le_integral hf.integrable (Eventually.of_forall fun y => (hf.pos y).le)

private theorem F_mono : Monotone (noiseCDF f) := fun _ _ hxy =>
  setIntegral_mono_set hf.integrable.integrableOn (Eventually.of_forall fun y => (hf.pos y).le)
    (Eventually.of_forall (Iic_subset_Iic.mpr hxy))

private theorem F_meas (m : ℝ) : Measurable fun x => noiseCDF f (x - m) :=
  (F_mono hf).measurable.comp (measurable_id.sub_const m)

private theorem F_shift (m x : ℝ) : ∫ s in Iic x, f (s - m) = noiseCDF f (x - m) := by
  rw [← integral_indicator measurableSet_Iic, noiseCDF, ← integral_indicator measurableSet_Iic]
  have : ∫ s, (Iic x).indicator (fun s => f (s - m)) s =
      ∫ s, (Iic (x - m)).indicator f (s - m) := by
    congr 1; funext s
    simp only [Set.indicator, mem_Iic, sub_le_sub_iff_right]
  rw [this, integral_sub_right_eq_self (fun s => (Iic (x - m)).indicator f s) m]

private theorem F_tendsto : Tendsto (noiseCDF f) atTop (𝓝 1) := by
  have := tendsto_setIntegral_of_monotone (μ := volume) (f := f)
    (s := fun x : ℝ => Iic x) (fun _ => measurableSet_Iic)
    (fun _ _ h => Iic_subset_Iic.mpr h) hf.integrable.integrableOn
  rw [iUnion_Iic, Measure.restrict_univ, hf.integral_eq_one] at this
  exact this

end

theorem solution {N : ℕ} (f : ℝ → ℝ) (hf : IsNoiseDensity f)
    (μ : Fin N → ℝ) (S : Finset (Fin N)) :
    ∑ i ∈ S, choiceProb f μ S i + noPurchaseProb f μ S = 1 := by
  classical
  set F := noiseCDF f with hFdef
  let G : Finset (Fin N) → ℝ → ℝ := fun S x => (∏ j ∈ S, F (x - μ j)) * F x
  let g : Finset (Fin N) → ℝ → ℝ := fun S x => (∏ j ∈ S, F (x - μ j)) * f x +
    ∑ i ∈ S, (∏ j ∈ S.erase i, F (x - μ j)) * F x * f (x - μ i)
  have hFm : Measurable F := (F_mono hf).measurable
  have hprod_meas : ∀ T : Finset (Fin N), Measurable fun x => ∏ j ∈ T, F (x - μ j) :=
    fun T => Finset.measurable_prod _ fun j _ => F_meas hf (μ j)
  have hprod_bd : ∀ T : Finset (Fin N), ∀ x, ‖∏ j ∈ T, F (x - μ j)‖ ≤ 1 := fun T x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun j _ => F_nonneg hf _)]
    exact Finset.prod_le_one (fun j _ => F_nonneg hf _) (fun j _ => F_le_one hf _)
  have hG_meas : ∀ T, Measurable (G T) := fun T => (hprod_meas T).mul hFm
  have hG_bd : ∀ T x, ‖G T x‖ ≤ 1 := fun T x => by
    simp only [G, norm_mul]
    have := hprod_bd T x
    have h2 : ‖F x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (F_nonneg hf x)]; exact F_le_one hf x
    nlinarith [norm_nonneg (∏ j ∈ T, F (x - μ j)), norm_nonneg (F x)]
  have hfs : ∀ m : ℝ, Integrable fun x => f (x - m) := fun m => hf.integrable.comp_sub_right m
  have hterm : ∀ T : Finset (Fin N), ∀ i, Integrable fun x =>
      (∏ j ∈ T, F (x - μ j)) * F x * f (x - μ i) := fun T i =>
    (hfs (μ i)).bdd_mul (hG_meas T).aestronglyMeasurable (Eventually.of_forall (hG_bd T))
  have hterm0 : ∀ T : Finset (Fin N), Integrable fun x => (∏ j ∈ T, F (x - μ j)) * f x :=
    fun T => hf.integrable.bdd_mul (hprod_meas T).aestronglyMeasurable
      (Eventually.of_forall (hprod_bd T))
  have hg_int : ∀ T, Integrable (g T) := fun T =>
    (hterm0 T).add (integrable_finsetSum _ fun i _ => hterm (T.erase i) i)
  -- the CDF identity
  have key : ∀ T : Finset (Fin N), ∀ x, ∫ s in Iic x, g T s = G T x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro x
      simp only [g, G, Finset.prod_empty, one_mul, Finset.sum_empty, add_zero]
      rfl
    | insert k T hk ih =>
      intro x
      have hpt : ∀ s, g (insert k T) s = f (s - μ k) * G T s + F (s - μ k) * g T s := by
        intro s
        simp only [g, G]
        rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.erase_insert hk, mul_add,
          Finset.mul_sum]
        have : ∀ i ∈ T, (∏ j ∈ (insert k T).erase i, F (s - μ j)) * F s * f (s - μ i) =
            F (s - μ k) * ((∏ j ∈ T.erase i, F (s - μ j)) * F s * f (s - μ i)) := by
          intro i hi
          have hne : k ≠ i := fun h => hk (h ▸ hi)
          rw [Finset.erase_insert_of_ne hne, Finset.prod_insert
            (fun h => hk (Finset.mem_of_mem_erase h))]
          ring
        rw [Finset.sum_congr rfl this]
        ring
      have hA : ∀ t, ∫ s in Iic t, f (s - μ k) = F (t - μ k) := F_shift hf (μ k)
      have hib := ibp_Iic (fun s => f (s - μ k)) (g T) (hfs (μ k)) (hg_int T) x
      simp only [hA, ih] at hib
      have i1 : Integrable fun s => f (s - μ k) * G T s := by
        have := (hfs (μ k)).bdd_mul (hG_meas T).aestronglyMeasurable
          (Eventually.of_forall (hG_bd T))
        simpa [mul_comm] using this
      have i2 : Integrable fun s => F (s - μ k) * g T s := by
        refine (hg_int T).bdd_mul (c := 1) (F_meas hf (μ k)).aestronglyMeasurable
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (F_nonneg hf _)]; exact F_le_one hf _
      rw [show (fun s => g (insert k T) s) = fun s =>
          f (s - μ k) * G T s + F (s - μ k) * g T s from funext hpt,
        integral_add i1.integrableOn i2.integrableOn, hib]
      simp only [G]
      rw [Finset.prod_insert hk]
      ring
  -- total mass
  have htot : ∫ s, g S s = 1 := by
    have h1 := tendsto_setIntegral_of_monotone (μ := volume) (f := g S)
      (s := fun x : ℝ => Iic x) (fun _ => measurableSet_Iic)
      (fun _ _ h => Iic_subset_Iic.mpr h) (hg_int S).integrableOn
    rw [iUnion_Iic, Measure.restrict_univ] at h1
    have h2 : Tendsto (G S) atTop (𝓝 1) := by
      have : Tendsto (G S) atTop (𝓝 ((∏ j ∈ S, (1 : ℝ)) * 1)) := by
        refine Tendsto.mul (tendsto_finset_prod _ fun j _ => ?_) (F_tendsto hf)
        exact (F_tendsto hf).comp (tendsto_atTop_add_const_right _ (-μ j) tendsto_id)
      simpa using this
    simp only [key] at h1
    exact tendsto_nhds_unique h1 h2
  rw [← htot]
  simp only [g]
  rw [integral_add (hterm0 S) (integrable_finsetSum _ fun i _ => hterm (S.erase i) i),
    integral_finset_sum _ fun i _ => hterm (S.erase i) i, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp [choiceProb, hi, F]
