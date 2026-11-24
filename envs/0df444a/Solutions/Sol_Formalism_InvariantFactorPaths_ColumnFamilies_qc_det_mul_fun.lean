-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_det_mul_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.440233+00:00
-- url     : https://prove2.me/submissions/fad06381-1eb6-4f4d-bca4-828639ae003f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  have h : (A * B) = fun a => ∑ k, A a k • B k := by
    funext a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 : (A * B).det = Matrix.detRowAlternating (fun a => ∑ k, A a k • B k) := by
    rw [← h]; rfl
  rw [h2]
  have h3 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_sum
    (fun a k => A a k • B k)
  erw [h3]
  apply Finset.sum_congr rfl
  intro f _
  have h4 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_smul_univ
    (fun a => A a (f a)) (fun a => B (f a))
  erw [h4]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
