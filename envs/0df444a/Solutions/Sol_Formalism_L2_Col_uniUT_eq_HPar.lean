-- Prove2me | solution 1 for Formalism.L2.Col.uniUT_eq_HPar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:31.336092+00:00
-- url     : https://prove2.me/submissions/5374dff3-4599-4856-b0ef-75e9ead50b56

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
theorem _root_.solution {r : ℕ} (h : r ≤ n) (bl : List ℕ) : uniUT n κ r bl = HPar n κ h bl (HU κ r) := by
  ext M
  unfold HPar
  rw [Subgroup.mem_map]
  constructor
  · intro hM
    refine ⟨⟨M, uniUT_le_blockUT n κ r bl hM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    obtain ⟨h1, h2⟩ := id hM
    show blk0 n κ h bl ⟨M, uniUT_le_blockUT n κ r bl hM⟩ ∈ btG r κ (fine r []) ∧
      ∀ i : Fin r, i.val < r → ((blk0 n κ h bl ⟨M, uniUT_le_blockUT n κ r bl hM⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i i = 1
    refine ⟨?_, fun i _ => ?_⟩
    · show (restr h (M : Matrix (Fin n) (Fin n) κ)).BlockTriangular (fun i => fine r [] i.val)
      intro i j hij
      exact h1 (i := Fin.castLE h i) (j := Fin.castLE h j)
        ((fine_lt_right (bl := bl) (show (Fin.castLE h i).val < r from i.2)).mpr ((fine_lt_right (bl := []) i.2).mp hij))
    · show restr h (M : Matrix (Fin n) (Fin n) κ) i i = 1
      exact h2 (Fin.castLE h i) i.2
  · rintro ⟨M', hM', rfl⟩
    rw [Subgroup.mem_comap] at hM'
    obtain ⟨h1, h2⟩ := hM'
    have hB := M'.2
    show (M' : GL (Fin n) κ) ∈ btG n κ (fine r bl) ∧ ∀ i : Fin n, i.val < r → ((M' : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i i = 1
    refine ⟨?_, fun i hi => h2 ⟨i.val, hi⟩ hi⟩
    show ((M' : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine r bl i.val)
    intro i j hij
    have hij' : fine r bl j.val < fine r bl i.val := hij
    by_cases hi : i.val < r
    · have hfi : fine r bl i.val = i.val := by simp only [fine, if_pos hi]
      have hj : j.val < r := by
        by_contra hj
        have hfj : fine r bl j.val = r + blkIdx bl (j.val - r) := by simp only [fine, if_neg hj]
        omega
      have hfj : fine r bl j.val = j.val := by simp only [fine, if_pos hj]
      exact h1 (i := ⟨i.val, hi⟩) (j := ⟨j.val, hj⟩)
        (show fine r [] j.val < fine r [] i.val by simp only [fine, if_pos hi, if_pos hj]; omega)
    · apply hB
      show coarse r bl j.val < coarse r bl i.val
      have hfi : fine r bl i.val = r + blkIdx bl (i.val - r) := by simp only [fine, if_neg hi]
      have hci : coarse r bl i.val = blkIdx bl (i.val - r) + 1 := by simp only [coarse, blkIdx, if_neg hi]
      rw [hci]
      by_cases hj : j.val < r
      · have hcj : coarse r bl j.val = 0 := by simp only [coarse, blkIdx, if_pos hj]
        omega
      · have hfj : fine r bl j.val = r + blkIdx bl (j.val - r) := by simp only [fine, if_neg hj]
        have hcj : coarse r bl j.val = blkIdx bl (j.val - r) + 1 := by simp only [coarse, blkIdx, if_neg hj]
        omega
end Formalism.L2.Col
