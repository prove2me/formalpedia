-- Prove2me | solution 1 for BidPriceControl.Asymptotic.overflow_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:03:58.439747+00:00
-- url     : https://prove2.me/submissions/49e4d652-ad94-48ee-8062-c0c07aa66b0e

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model
import Theorems.Thm_BidPriceControl_Asymptotic_gallego_bound
import Theorems.Thm_BidPriceControl_Asymptotic_seats_mean_variance
import Theorems.Thm_BidPriceControl_Asymptotic_kuhn_tucker_conditions

open MeasureTheory ProbabilityTheory

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ)
    (i : Fin m) :
    ∫ ω, max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0
        ∂(pathMeasure (scaledLaw F θ) (θ * k))
      ≤ Real.sqrt (variance (seatsCounted A μstar i) (pathMeasure (scaledLaw F θ) (θ * k))) / 2 := by
  -- the scaled laws used by the path measure are probability measures
  have hθ0 : 0 < θ := hθ
  have hprob : ∀ s : Fin (θ * k), IsProbabilityMeasure (scaledLaw F θ (θ * k - (s : ℕ))) := by
    intro s
    have hs := s.isLt
    refine (hF _ ?_).isProbabilityMeasure
    rw [Finset.mem_Icc]
    constructor
    · rw [Nat.le_div_iff_mul_le hθ0]; omega
    · rw [Nat.div_le_iff_le_mul_add_pred hθ0]
      have : θ * k = k * θ := mul_comm _ _
      omega
  haveI : IsProbabilityMeasure (pathMeasure (scaledLaw F θ) (θ * k)) := by
    unfold pathMeasure
    infer_instance
  set P := pathMeasure (scaledLaw F θ) (θ * k)
  set Z := seatsCounted A μstar i
  -- Z is a bounded measurable random variable, hence in L²
  have hZm : Measurable Z := by
    unfold Z seatsCounted
    refine Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun j _ => ?_
    exact Measurable.ite (measurableSet_lt measurable_const
      ((measurable_pi_apply j).comp (measurable_pi_apply s))) measurable_const measurable_const
  have hZb : ∀ ω, ‖Z ω‖ ≤ ∑ s : Fin (θ * k), ∑ j, (A i j : ℝ) := by
    intro ω
    have h0 : 0 ≤ Z ω := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun j _ => by
      split_ifs <;> simp
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun j _ => by
      split_ifs <;> simp
  have hZ : MemLp Z 2 P :=
    MemLp.of_bound hZm.aestronglyMeasurable _ (Filter.Eventually.of_forall hZb)
  have hg := gallego_bound P Z hZ ((θ : ℝ) * (x i : ℝ))
  have hmean := (seats_mean_variance A F k x hF μstar hmin θ hθ i).1
  have hkt := (kuhn_tucker_conditions A F k x hF μstar hmin i).1
  set d := (θ : ℝ) * (x i : ℝ) - ∫ ω, Z ω ∂P with hd
  have hd0 : 0 ≤ d := by
    rw [hd]
    change 0 ≤ (θ : ℝ) * (x i : ℝ) - ∫ ω, seatsCounted A μstar i ω ∂P
    rw [hmean]
    have : (0 : ℝ) ≤ θ := Nat.cast_nonneg θ
    nlinarith
  set V := variance Z P
  have hV : 0 ≤ V := variance_nonneg Z P
  have hsq : Real.sqrt (V + d ^ 2) ≤ Real.sqrt V + d := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hV, Real.sqrt_nonneg V]
  calc ∫ ω, max (Z ω - (θ : ℝ) * (x i : ℝ)) 0 ∂P ≤ (Real.sqrt (V + d ^ 2) - d) / 2 := hg
    _ ≤ Real.sqrt V / 2 := by linarith
