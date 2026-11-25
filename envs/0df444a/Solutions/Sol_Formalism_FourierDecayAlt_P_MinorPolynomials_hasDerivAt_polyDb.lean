-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_polyDb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:25:49.368431+00:00
-- url     : https://prove2.me/submissions/855302c2-244d-43df-ab04-cdf418950596

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsVecApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetClassEstimate
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_qDbl_eval
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_poly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    HasDerivAt (fun t => star (Dmin k r z z' (crv (false, X) g t) l)) (eval (vars g) (dP X (qDbl z z' l))) 0 := by
  have h := hasDerivAt_poly X g (qDbl (k := k) z z' l)
  simp only [qDbl_eval] at h
  exact h
end Formalism.FourierDecayAlt.P.MinorPolynomials
