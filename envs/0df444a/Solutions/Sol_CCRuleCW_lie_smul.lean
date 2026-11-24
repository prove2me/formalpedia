-- Prove2me | solution 1 for CCRuleCW.lie_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:13:55.129923+00:00
-- url     : https://prove2.me/submissions/cd07a510-9a29-4cec-9eda-01c925dfcc41

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate Nat
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
variable {n : ℕ}
namespace CCRuleCW
theorem _root_.solution (H X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ * H + H * X = 0) (c : ℝ) :
    ((c : ℂ) • X)ᴴ * H + H * ((c : ℂ) • X) = 0 := by
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]
end CCRuleCW
