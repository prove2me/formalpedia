-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qhM_full
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:46.253124+00:00
-- url     : https://prove2.me/submissions/96607383-ee62-4979-982e-916738f37c9a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (J : ℕ → Fin n) : ∃ ε : R, qhM R n J = ε • ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) := by
  unfold qhM
  rw [dif_pos le_rfl]
  unfold qhN
  by_cases hJ : Function.Injective (fun q : Fin n => J q.val)
  · let σ : Equiv.Perm (Fin n) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hJ)
    refine ⟨((Equiv.Perm.sign σ : ℤ) : R), ?_⟩
    have hM : (Matrix.of fun p q : Fin n => genMat R n (Fin.castLE le_rfl p) (J q.val)) =
        (genMat R n).submatrix id σ := by
      ext p q
      simp [σ]
    rw [hM, Matrix.det_permute']
    change _ = _ • algebraMap _ (GLCoord R n) (genMat R n).det
    simp [Algebra.smul_def, map_mul, map_intCast]
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hJ
    refine ⟨0, ?_⟩
    have hz : (Matrix.of fun p q : Fin n => genMat R n (Fin.castLE le_rfl p) (J q.val)).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.of_apply, hab])
    simp only [hz, map_zero, zero_smul]
end Formalism.InvariantFactorPaths.ColumnFamilies
