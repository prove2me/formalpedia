-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_evGL_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:23.805987+00:00
-- url     : https://prove2.me/submissions/41b94590-017c-4c72-a94b-a977d84bbc98

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra ℚ R'] (γ : GL (Fin n) ℚ) (z : GLCoord ℤ n) :
    evGL (Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) z = algebraMap ℚ R' (evGL γ z) := by
  have h : evGL (Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) = (algebraMap ℚ R').comp (evGL γ) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [evGL, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ z) h
end Formalism.InvariantFactorPaths.ColumnFamilies
