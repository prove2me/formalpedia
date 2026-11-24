-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.hh_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:55:14.045094+00:00
-- url     : https://prove2.me/submissions/8fb303d4-c0df-4b83-9e5a-ebdf917bb10c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolynomialBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_hh_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (j : ℕ) {x : ℝ} (hx : ε ≤ x) :
    ‖iteratedFDeriv ℝ j (hh ε) x‖ ≤ |(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) := by
  have hx0 : 0 < x := lt_of_lt_of_le hε hx
  have h2 : ε / 2 < x := by linarith
  have heq : iteratedFDeriv ℝ j (hh ε) x = iteratedFDeriv ℝ j (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) x := by
    first
    | exact ((hh_ev hε h2).iteratedFDeriv ℝ j).eq_of_nhds
    | exact (hh_ev hε h2).iteratedFDeriv_eq j
  rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hexp : -(1 / 2 : ℝ) - j ≤ 0 := by linarith
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  first
  | exact Real.rpow_le_rpow_of_exponent_nonpos hε hx hexp
  | exact Real.rpow_le_rpow_of_nonpos hε hx hexp
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
