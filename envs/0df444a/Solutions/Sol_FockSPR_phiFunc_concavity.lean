-- Prove2me | solution 1 for FockSPR.phiFunc_concavity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:49.778811+00:00
-- url     : https://prove2.me/submissions/a9c57c88-4836-423a-a946-8944d77534c8

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
section
@[expose] public section
open Real MeasureTheory Set
noncomputable section
namespace FockSPR
private lemma hasDerivAt_phiFunc (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (phiFunc n) ((2 * ↑n + 1) / r - 2 * r) r := by
  unfold phiFunc
  have h1 := (Real.hasDerivAt_log (ne_of_gt hr)).const_mul (2 * ↑n + 1 : ℝ)
  have h2 : HasDerivAt (fun r => r ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have h3 := h1.sub h2
  rw [show (2 * (n : ℝ) + 1) / r - 2 * r = (2 * ↑n + 1) * r⁻¹ - 2 * r by
    rw [div_eq_mul_inv]]
  exact h3
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Set
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    StrictConcaveOn ℝ (Ioi 0) (phiFunc n) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
  · unfold phiFunc
    apply ContinuousOn.sub
    · apply ContinuousOn.mul continuousOn_const
      exact Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
    · exact continuousOn_pow 2
  · rw [interior_Ioi]
    intro a ha b hb hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    rw [(hasDerivAt_phiFunc n ha').deriv, (hasDerivAt_phiFunc n hb').deriv]
    have hnn : (0 : ℝ) < 2 * ↑n + 1 := by positivity
    linarith only [hab, ha', hnn, div_lt_div_of_pos_left hnn ha' hab]
end FockSPR
