-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_capped_killed_record_esscher_fullpath_clock_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:56:23.468016+00:00
-- url     : https://prove2.me/submissions/7bd77b80-5d61-4382-acc2-7bcb85d986a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_record_exp_clock_fullPath_esscher_mixture

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal


lemma s229_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure ℝ) [SFinite P] [SFinite μ]
    (a : Ω → ℝ≥0∞) (G : Ω × ℝ → ℝ≥0∞) (K : Ω → ℝ → ℝ≥0∞) (ha : Measurable a) (hG : Measurable G)
    (h : ∀ ω u, a ω * G (ω, u) = K ω u) :
    ∫⁻ ω, a ω * ∫⁻ u, G (ω, u) ∂μ ∂P = ∫⁻ u, ∫⁻ ω, K ω u ∂P ∂μ := by
  calc ∫⁻ ω, a ω * ∫⁻ u, G (ω, u) ∂μ ∂P = ∫⁻ ω, ∫⁻ u, a ω * G (ω, u) ∂μ ∂P :=
        lintegral_congr (fun ω => (lintegral_const_mul _ (hG.comp measurable_prodMk_left)).symm)
    _ = ∫⁻ u, ∫⁻ ω, a ω * G (ω, u) ∂P ∂μ :=
        lintegral_lintegral_swap ((ha.comp measurable_fst).mul hG).aemeasurable
    _ = ∫⁻ u, ∫⁻ ω, K ω u ∂P ∂μ := by simp_rw [h]

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    [hDec : DecidablePred (fun ω : Ω => ω ∈ A)]
    (hτdef : τ = fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (hAdef : A =
      {ω : Ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
      {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)})
    (hτ : Measurable τ) (hA : MeasurableSet A)
    (W : Ω → ℝ≥0∞)
    (hW : ∀ ω : Ω, W ω = if ω ∈ A then 1 else 0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hWeight : ∀ ω : Ω, ω ∈ A →
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) * ENNReal.ofReal (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) = discount (τ ω))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : ∀ u : ℝ≥0, Measurable (H u))
    (hRMeas : Measurable (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal r) ω - (Real.toNNReal r : ℝ) * X.ψ θ)) * H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)))
    (hPostMeas : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 - X.X (τ z.1) z.1) - (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
      H (Real.toNNReal z.2) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hObserve : Measurable (fun z : Ω × ℝ =>
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ))) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hReward : Measurable (fun z : Ω × ℝ =>
      (W z.1 * ENNReal.ofReal (Real.exp (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
      (ENNReal.ofReal (Real.exp (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 - X.X (τ z.1) z.1) - (Real.toNNReal z.2 : ℝ) * X.ψ θ)) * H (Real.toNNReal z.2) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))))
    (hSplit : ∀ (ω : Ω) (t : ℝ), (τ ω : ℝ) ≤ t →
      ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) *
      ENNReal.ofReal (Real.exp (θ * (X.X (τ ω + Real.toNNReal (t - (τ ω : ℝ))) ω - X.X (τ ω) ω) - (Real.toNNReal (t - (τ ω : ℝ)) : ℝ) * X.ψ θ))) :
    (∫⁻ z : Ω × ℝ,
      if (τ z.1 : ℝ) ≤ z.2 then W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ))) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      else 0
      ∂((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ r : ℝ, (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal r) ω - (Real.toNNReal r : ℝ) * X.ψ θ)) * H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P) ∂(expMeasure p)) := by
  rw [avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral X θ p hp τ hτ W H
    hJoint hObserve hReward hSplit]
  have : SFinite (expMeasure p) := by unfold expMeasure gammaMeasure; infer_instance
  have ha : Measurable fun ω => ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) := by fun_prop
  refine (s229_aux P (expMeasure p) _ _ (fun ω r => if ω ∈ A then discount (τ ω) *
         (ENNReal.ofReal (Real.exp
           (θ * (X.X (τ ω + Real.toNNReal r) ω - X.X (τ ω) ω) -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
          H (Real.toNNReal r) (fun t : ℝ≥0 =>
            X.X (τ ω + t) ω - X.X (τ ω) ω))
         else 0) ha hReward ?_).trans ?_
  · intro ω u
    by_cases hA : ω ∈ A
    · simp only [hA, if_true, hW, one_mul]
      rw [← hWeight ω hA]; ring
    · simp [hA, hW]
  · have hmix := avram_ws01h_killed_record_exp_clock_fullPath_esscher_mixture X lower b N θ p hθ hp
      discount hd H hH hRMeas
    subst hτdef hAdef
    convert hmix
