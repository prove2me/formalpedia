-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:30:11.839389+00:00
-- url     : https://prove2.me/submissions/be780fba-0273-47fc-a318-bbc2fc7c8b85

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution (hibp : RegIBP) : TestDecay := by
  unfold TestDecay
  unfold RegIBP at hibp
  intro wh hwh
  unfold om
  unfold IsTest at hwh
  obtain ⟨hcd, hcs, _⟩ := hwh
  have hcd' : ContDiff ℝ 2 (fun t : ℝ => (wh t : ℂ)) := by
    first
    | exact Complex.ofRealCLM.contDiff.comp hcd
    | fun_prop
  have hcs' : HasCompactSupport (fun t : ℝ => (wh t : ℂ)) := hcs.comp_left Complex.ofReal_zero
  have hgc : Continuous (fun t : ℝ => (wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) :=
    hcd'.continuous.sub (hcd'.continuous_iteratedDeriv 2 (by norm_num))
  have hgs : HasCompactSupport
      (fun t : ℝ => (wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) :=
    hcs'.sub (by
      first
      | (rw [iteratedDeriv_succ, iteratedDeriv_one]; exact hcs'.deriv.deriv)
      | (rw [iteratedDeriv_eq_iterate]; exact hcs'.deriv.deriv)
      | exact hcs'.iteratedDeriv 2)
  have hn : ∀ y : ℝ, ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := fun y => by
    rw [Complex.norm_exp]
    simp
  refine ⟨2 * ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖, fun x => ?_⟩
  have key := hibp (fun t : ℝ => (wh t : ℂ)) hcd' hcs' x
  beta_reduce at key
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hbound : ‖∫ t, ((wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) *
      Complex.exp (Complex.I * ↑(x * t))‖ ≤
      ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    rw [norm_mul, hn, mul_one]
  have e2 : ∫ τ, (wh τ : ℂ) * Complex.exp (Complex.I * ↑(τ * x)) =
      ∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t)) := by
    congr 1
    funext t
    rw [mul_comm t x]
  rw [e2]
  have hI : ‖∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))‖ * (1 + x ^ 2) ≤
      ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖ := by
    have h3 := congrArg norm key
    rw [norm_mul, Complex.norm_of_nonneg hpos.le] at h3
    rw [mul_comm, ← h3]
    exact hbound
  have hsq : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
  have hq : 0 < (1 + |x|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hq]
  have hm := mul_le_mul_of_nonneg_left hsq
    (norm_nonneg (∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))))
  nlinarith [hI, hm]
end Formalism.FourierDecayAlt.P.B1
