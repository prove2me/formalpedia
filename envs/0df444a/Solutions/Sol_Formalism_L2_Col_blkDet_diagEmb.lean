-- Prove2me | solution 1 for Formalism.L2.Col.blkDet_diagEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:53.331667+00:00
-- url     : https://prove2.me/submissions/d95fa70c-78fc-466e-8c73-badfb3ab550b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution {s : ℕ} (h : s ≤ n) (β : ℕ → ℕ) (c : ℕ) (hc : ∀ i : ℕ, s ≤ i → β i ≠ c) (g : GL (Fin s) κ)
    (hg : g ∈ btG s κ β) (hg' : diagEmb κ h g ∈ btG n κ β) :
    blkDet n κ β c ⟨diagEmb κ h g, hg'⟩ = blkDet s κ β c ⟨g, hg⟩ := by
  apply Units.ext
  change Matrix.det ((diagMat s n (g : Matrix (Fin s) (Fin s) κ)).toSquareBlock (fun i => β i.val) c) =
    Matrix.det ((g : Matrix (Fin s) (Fin s) κ).toSquareBlock (fun i => β i.val) c)
  let e : {i : Fin s // β i.val = c} ≃ {i : Fin n // β i.val = c} :=
    { toFun := fun i => ⟨⟨i.1.val, lt_of_lt_of_le i.1.2 h⟩, i.2⟩
      invFun := fun i => ⟨⟨i.1.val, by
        by_contra hh
        exact hc i.1.val (by omega) i.2⟩, i.2⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  have hb : (diagMat s n (g : Matrix (Fin s) (Fin s) κ)).toSquareBlock (fun i => β i.val) c =
      ((g : Matrix (Fin s) (Fin s) κ).toSquareBlock (fun i => β i.val) c).submatrix e.symm e.symm := by
    ext i j
    have hi : (i.1 : Fin n).val < s := by
      by_contra hh
      exact hc _ (by omega) i.2
    have hj : (j.1 : Fin n).val < s := by
      by_contra hh
      exact hc _ (by omega) j.2
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.submatrix_apply, diagMat]
    rw [dif_pos ⟨hi, hj⟩]
    rfl
  rw [hb, Matrix.det_submatrix_equiv_self]
end Formalism.L2.Col
