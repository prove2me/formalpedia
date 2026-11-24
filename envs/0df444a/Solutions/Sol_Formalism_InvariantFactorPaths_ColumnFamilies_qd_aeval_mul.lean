-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_aeval_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:51.138478+00:00
-- url     : https://prove2.me/submissions/ee367c0e-4ead-40fd-859e-ca39a6aa7c26

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
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1) P
      = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) (rowAct ℚ γ.val.transpose P) := by
  have h : aeval (R := ℚ) (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1)
      = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).comp (rowAct ℚ γ.val.transpose) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, rowAct, aeval_X, aeval_X, map_sum, Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_X, aeval_C, Matrix.transpose_apply, mul_comm]
    rfl
  exact congrArg (fun φ => φ P) h
end Formalism.InvariantFactorPaths.ColumnFamilies
