-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:47.138903+00:00
-- url     : https://prove2.me/submissions/1e6a894f-bb17-43ff-91ec-a4d9cfd6ca45

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (c : ℚ) :
    evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) c) = algebraMap ℚ R' c := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n), evGLR,
    IsLocalization.Away.lift_eq, MvPolynomial.algebraMap_eq, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
end Formalism.InvariantFactorPaths.ColumnFamilies
