-- Prove2me | solution 1 for DeletionCode.SignedSupport.gram_injective_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:18:07.248808+00:00
-- url     : https://prove2.me/submissions/01b24cb3-d1d8-4143-b515-1c4ce3d88186

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_source_vertices

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (side : Bool) :
    Function.Injective (fun i : Fin (F.extra b side + 1) => gram (F.path b side) L i.val) := by
  intro i j hij
  have he := gram_eq_source_vertices F L b b side side i.val j.val hij
  have hi := i.isLt
  have hj := j.isLt
  have hindices := H.simple b side
    (a₁ := ⟨i.val, by omega⟩) (a₂ := ⟨j.val, by omega⟩) he
  exact Fin.ext (congrArg (fun z : Fin (F.extra b side + 2) => z.val) hindices)
end DeletionCode.SignedSupport
