-- Prove2me | solution 1 for Formalism.L2.Col.HK_eq_HPar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:27.173186+00:00
-- url     : https://prove2.me/submissions/2edaf99b-4b24-4ae8-b5ac-021627fab14a

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
variable {n : ℕ} {κ : Type} [CommRing κ]
namespace Formalism.L2.Col
theorem _root_.solution {r : ℕ} (h : r ≤ n) (bl : List ℕ) : HK n κ r bl = HPar n κ h bl ⊥ := by
  unfold HK HPar
  congr 1
  ext M
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_bot]
  constructor
  · intro hM
    apply Units.ext
    ext i j
    show restr h (M.1 : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin r) (Fin r) κ) i j
    have hi0 : coarse r bl (Fin.castLE h i).val = 0 := by simp only [coarse, blkIdx, Fin.coe_castLE, if_pos i.2]
    have hj0 : coarse r bl (Fin.castLE h j).val = 0 := by simp only [coarse, blkIdx, Fin.coe_castLE, if_pos j.2]
    have hk := congrFun (congrFun hM ⟨Fin.castLE h i, hi0⟩) ⟨Fin.castLE h j, hj0⟩
    rw [blkHom_apply] at hk
    have hk' : restr h (M.1 : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix {x : Fin n // coarse r bl x.val = 0} {x : Fin n // coarse r bl x.val = 0} κ) ⟨Fin.castLE h i, hi0⟩ ⟨Fin.castLE h j, hj0⟩ := hk
    rw [hk']
    simp [Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]
  · intro hM
    ext i j
    rw [blkHom_apply]
    have hi : (i.1 : Fin n).val < r := by
      by_contra hh
      exact absurd i.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
    have hj : (j.1 : Fin n).val < r := by
      by_contra hh
      exact absurd j.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
    have hk := congrArg (fun X : GL (Fin r) κ => (X : Matrix (Fin r) (Fin r) κ) ⟨i.1.val, hi⟩ ⟨j.1.val, hj⟩) hM
    have hk' : (M.1 : Matrix (Fin n) (Fin n) κ) i.1 j.1 = (1 : Matrix (Fin r) (Fin r) κ) ⟨i.1.val, hi⟩ ⟨j.1.val, hj⟩ := hk
    rw [hk']
    simp [Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]
end Formalism.L2.Col
