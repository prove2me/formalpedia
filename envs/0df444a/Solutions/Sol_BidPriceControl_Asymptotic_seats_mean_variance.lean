-- Prove2me | solution 1 for BidPriceControl.Asymptotic.seats_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:08:06.154198+00:00
-- url     : https://prove2.me/submissions/713a75f1-f8ae-4af3-bb60-0108592d4a07

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

open MeasureTheory ProbabilityTheory

namespace Aux_BPC_smv
open BidPriceControl.Asymptotic

lemma sum_Icc_one (N : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ Finset.Icc 1 N, f t = ∑ u ∈ Finset.range N, f (u + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma block (θ : ℕ) (hθ : 1 ≤ θ) (G : ℕ → ℝ) (k : ℕ) :
    ∑ u ∈ Finset.range (θ * k), G ((u + θ) / θ) = (θ : ℝ) * ∑ u ∈ Finset.range k, G (u + 1) := by
  have hθ0 : 0 < θ := hθ
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    have : ∀ i ∈ Finset.range θ, G ((θ * k + i + θ) / θ) = G (k + 1) := by
      intro i hi
      have hi' : i < θ := Finset.mem_range.mp hi
      have e : θ * k + i + θ = i + θ * (k + 1) := by ring
      rw [e, Nat.add_mul_div_left _ _ hθ0, Nat.div_eq_of_lt hi', zero_add]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma block_Icc (θ : ℕ) (hθ : 1 ≤ θ) (G : ℕ → ℝ) (k : ℕ) :
    ∑ t ∈ Finset.Icc 1 (θ * k), G ((t + θ - 1) / θ) = (θ : ℝ) * ∑ t ∈ Finset.Icc 1 k, G t := by
  rw [sum_Icc_one, sum_Icc_one, ← block θ hθ G k]
  apply Finset.sum_congr rfl
  intro u _
  congr 2
  omega

lemma sum_fin_rev (K : ℕ) (f : ℕ → ℝ) :
    ∑ s : Fin K, f (K - (s : ℕ)) = ∑ t ∈ Finset.Icc 1 K, f t := by
  rw [Fin.sum_univ_eq_sum_range (fun u => f (K - u)) K, sum_Icc_one]
  rw [← Finset.sum_range_reflect (fun u => f (u + 1)) K]
  apply Finset.sum_congr rfl
  intro u hu
  have := Finset.mem_range.mp hu
  congr 1
  omega

/-- `Σ_j 1{r^j > μA^j} a_ij`, the leg-`i` seats requested in one period. -/
noncomputable def H {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (i : Fin m)
    (r : Fin n → ℝ) : ℝ :=
  ∑ j, if bidSum A μ j < r j then (A i j : ℝ) else 0

lemma ite_measurable {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (j : Fin n) (c : ℝ) :
    Measurable (fun r : Fin n → ℝ => if bidSum A μ j < r j then c else 0) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
    measurable_const measurable_const

lemma H_measurable {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (i : Fin m) :
    Measurable (H A μ i) := by
  unfold H
  exact Finset.measurable_sum _ fun j _ => ite_measurable A μ j _

lemma H_memLp {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (i : Fin m)
    (G : Measure (Fin n → ℝ)) [IsProbabilityMeasure G] : MemLp (H A μ i) 2 G := by
  refine MemLp.of_bound (H_measurable A μ i).aestronglyMeasurable (∑ j, (A i j : ℝ))
    (Filter.Eventually.of_forall fun r => ?_)
  have h0 : 0 ≤ H A μ i r := Finset.sum_nonneg fun j _ => by split_ifs <;> simp
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact Finset.sum_le_sum fun j _ => by split_ifs <;> simp

lemma integral_ite {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (j : Fin n) (c : ℝ)
    (G : Measure (Fin n → ℝ)) [IsProbabilityMeasure G] :
    ∫ r, (if bidSum A μ j < r j then c else 0) ∂G = (G {r | bidSum A μ j < r j}).toReal * c := by
  have : (fun r : Fin n → ℝ => if bidSum A μ j < r j then c else 0)
      = Set.indicator {r | bidSum A μ j < r j} (fun _ => c) := by
    funext r; simp [Set.indicator]
  rw [this, integral_indicator_const _
    (measurableSet_lt measurable_const (measurable_pi_apply j))]
  simp [Measure.real]

lemma integral_H {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (i : Fin m)
    (G : Measure (Fin n → ℝ)) [IsProbabilityMeasure G] :
    ∫ r, H A μ i r ∂G = ∑ j, (G {r | bidSum A μ j < r j}).toReal * (A i j : ℝ) := by
  unfold H
  rw [integral_finsetSum _ fun j _ => ?_]
  · exact Finset.sum_congr rfl fun j _ => integral_ite A μ j _ G
  · exact Integrable.of_bound (ite_measurable A μ j _).aestronglyMeasurable |(A i j : ℝ)|
      (Filter.Eventually.of_forall fun r => by split_ifs <;> simp)

lemma H_sq {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ) (i : Fin m)
    (r : Fin n → ℝ) (hr : InS r) :
    H A μ i r ^ 2 = ∑ j, if bidSum A μ j < r j then (A i j : ℝ) ^ 2 else 0 := by
  have hb : ∀ j, 0 ≤ bidSum A μ j := fun j =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (Nat.cast_nonneg _)
  unfold H
  by_cases hex : ∃ j0, bidSum A μ j0 < r j0
  · obtain ⟨j0, hj0⟩ := hex
    have hother : ∀ j, j ≠ j0 → ¬ bidSum A μ j < r j := by
      intro j hj hlt
      exact hj (hr.2 j j0 (lt_of_le_of_lt (hb j) hlt) (lt_of_le_of_lt (hb j0) hj0))
    rw [Finset.sum_eq_single j0 (fun j _ hj => by simp [hother j hj]) (by simp),
      Finset.sum_eq_single j0 (fun j _ hj => by simp [hother j hj]) (by simp)]
    simp [hj0]
  · push Not at hex
    simp [fun j => not_lt.mpr (hex j)]

lemma var_H_le {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ) (i : Fin m)
    (G : Measure (Fin n → ℝ)) (hG : IsRequestLaw G) :
    variance (H A μ i) G ≤
      ∑ j, (A i j : ℝ) ^ 2 * (G {r | bidSum A μ j < r j}).toReal *
        (1 - (G {r | bidSum A μ j < r j}).toReal) := by
  haveI := hG.isProbabilityMeasure
  rw [variance_eq_sub (H_memLp A μ i G)]
  set p : Fin n → ℝ := fun j => (G {r | bidSum A μ j < r j}).toReal with hp
  have hsq : ∫ r, (H A μ i ^ 2) r ∂G = ∑ j, p j * (A i j : ℝ) ^ 2 := by
    have hae : (H A μ i ^ 2) =ᵐ[G]
        fun r => ∑ j, if bidSum A μ j < r j then (A i j : ℝ) ^ 2 else 0 :=
      hG.ae_inS.mono fun r hr => by simp only [Pi.pow_apply]; exact H_sq A μ hμ i r hr
    rw [integral_congr_ae hae, integral_finsetSum _ fun j _ => ?_]
    · exact Finset.sum_congr rfl fun j _ => integral_ite A μ j _ G
    · exact Integrable.of_bound (ite_measurable A μ j _).aestronglyMeasurable
        |(A i j : ℝ) ^ 2| (Filter.Eventually.of_forall fun r => by split_ifs <;> simp)
  have hmean : ∫ r, H A μ i r ∂G = ∑ j, p j * (A i j : ℝ) := integral_H A μ i G
  have hmean' : G[H A μ i] = ∑ j, p j * (A i j : ℝ) := hmean
  have hsq' : G[H A μ i ^ 2] = ∑ j, p j * (A i j : ℝ) ^ 2 := hsq
  rw [hmean', hsq']
  have hp0 : ∀ j, 0 ≤ p j := fun j => ENNReal.toReal_nonneg
  have hcs : ∑ j, (p j * (A i j : ℝ)) ^ 2 ≤ (∑ j, p j * (A i j : ℝ)) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => mul_nonneg (hp0 j) (Nat.cast_nonneg _)
  have : ∑ j, (A i j : ℝ) ^ 2 * p j * (1 - p j)
      = ∑ j, p j * (A i j : ℝ) ^ 2 - ∑ j, (p j * (A i j : ℝ)) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  linarith

end Aux_BPC_smv

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) (i : Fin m) :
    ∫ ω, seatsCounted A μstar i ω ∂(pathMeasure (scaledLaw F θ) (θ * k))
        = (θ : ℝ) * ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ) ∧
      variance (seatsCounted A μstar i) (pathMeasure (scaledLaw F θ) (θ * k))
        ≤ (θ : ℝ) * ∑ t ∈ Finset.Icc 1 k, ∑ j, indicatorVar A F μstar i t j := by
  have hθ0 : 0 < θ := hθ
  set K := θ * k with hK
  have hRL : ∀ s : Fin K, IsRequestLaw (scaledLaw F θ (K - (s : ℕ))) := by
    intro s
    have hs := s.isLt
    refine hF _ ?_
    rw [Finset.mem_Icc]
    constructor
    · rw [Nat.le_div_iff_mul_le hθ0]; omega
    · rw [Nat.div_le_iff_le_mul_add_pred hθ0]
      have : θ * k = k * θ := mul_comm _ _
      omega
  haveI hprob : ∀ s : Fin K, IsProbabilityMeasure (scaledLaw F θ (K - (s : ℕ))) :=
    fun s => (hRL s).isProbabilityMeasure
  have hseat : seatsCounted A μstar i
      = ∑ s : Fin K, fun ω : Fin K → Fin n → ℝ => Aux_BPC_smv.H A μstar i (ω s) := by
    funext ω
    simp [seatsCounted, Aux_BPC_smv.H, Finset.sum_apply]
  constructor
  · unfold pathMeasure
    rw [hseat]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun s _ => ?_]
    · have : ∀ s : Fin K, ∫ ω : Fin K → Fin n → ℝ, Aux_BPC_smv.H A μstar i (ω s)
            ∂(Measure.pi fun s : Fin K => scaledLaw F θ (K - (s : ℕ)))
          = (fun t => ∑ j, exceedProb A (scaledLaw F θ) μstar t j * (A i j : ℝ)) (K - (s : ℕ)) := by
        intro s
        rw [integral_comp_eval (Aux_BPC_smv.H_measurable A μstar i).aestronglyMeasurable,
          Aux_BPC_smv.integral_H]
        rfl
      rw [Finset.sum_congr rfl fun s _ => this s]
      exact (Aux_BPC_smv.sum_fin_rev K _).trans (Aux_BPC_smv.block_Icc θ hθ
        (fun t => ∑ j, exceedProb A F μstar t j * (A i j : ℝ)) k)
    · exact ((Aux_BPC_smv.H_memLp A μstar i _).comp_measurePreserving
        (measurePreserving_eval _ s)).integrable one_le_two
  · unfold pathMeasure
    rw [hseat, variance_sum_pi (fun s => Aux_BPC_smv.H_memLp A μstar i _)]
    calc ∑ s : Fin K, variance (Aux_BPC_smv.H A μstar i) (scaledLaw F θ (K - (s : ℕ)))
        ≤ ∑ s : Fin K, (fun t => ∑ j, indicatorVar A (scaledLaw F θ) μstar i t j) (K - (s : ℕ)) :=
          Finset.sum_le_sum fun s _ => Aux_BPC_smv.var_H_le A μstar hmin.1 i _ (hRL s)
      _ = _ := by
          exact (Aux_BPC_smv.sum_fin_rev K _).trans
            (Aux_BPC_smv.block_Icc θ hθ (fun t => ∑ j, indicatorVar A F μstar i t j) k)
