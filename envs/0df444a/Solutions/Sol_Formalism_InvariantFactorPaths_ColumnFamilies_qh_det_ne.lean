-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:23.792815+00:00
-- url     : https://prove2.me/submissions/85a17cd4-1590-4e52-9667-0566712e923e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [IsDomain R] {B : Type} [CommRing B] (φ : MvPolynomial (Fin n × Fin n) R →+* B)
    (hφ : Function.Injective φ) : (Matrix.of fun a c : Fin n => φ (X (c, a))).det ≠ 0 := by
  have h : (Matrix.of fun a c : Fin n => φ (X (c, a))) =
      (φ.mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) R)).transpose := by
    ext a c; simp [Matrix.mvPolynomialX]
  rw [h, Matrix.det_transpose, ← RingHom.map_det, map_ne_zero_iff _ hφ]
  exact Matrix.det_mvPolynomialX_ne_zero _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
