-- Prove2me | solution 1 for BetaCoskew.ThreeMoment.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:37:15.085014+00:00
-- url     : https://prove2.me/submissions/55c2cebe-c6b2-47e4-9a3c-aeeaf573f908

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

open MeasureTheory ProbabilityTheory

open BetaCoskew.ThreeMoment in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (u w : ℝ → ℝ) (rf : ℝ)
    (mt RM : Ω → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hmt : Integrable mt P)
    (hg : Integrable (fun ω =>
      deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω)) P)
    (hrf : (∫ ω, mt ω ∂P) * (1 + rf) = 1)
    (hkernel : mt =ᵐ[P] fun ω => lam⁻¹ *
      (deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω))) :
    lam = (1 + rf) * kernelMean P u w RM ∧
      mt =ᵐ[P] fun ω => mFun P u w rf RM (RM ω) := by
  have hint : ∫ ω, mt ω ∂P = lam⁻¹ * kernelMean P u w RM := by
    unfold kernelMean
    rw [integral_congr_ae hkernel, integral_const_mul]
  have hne : lam ≠ 0 := hlam.ne'
  have hl : lam = (1 + rf) * kernelMean P u w RM := by
    have h2 : lam⁻¹ * kernelMean P u w RM * (1 + rf) = 1 := by rw [← hint]; exact hrf
    calc lam = lam * (lam⁻¹ * kernelMean P u w RM * (1 + rf)) := by rw [h2, mul_one]
      _ = (1 + rf) * kernelMean P u w RM := by
        simp only [← mul_assoc, mul_inv_cancel₀ hne, one_mul]; ring
  refine ⟨hl, hkernel.mono fun ω h => ?_⟩
  beta_reduce at h ⊢
  rw [h, mFun, ← hl]
  ring
