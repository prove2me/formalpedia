-- Prove2me | solution 1 for DeletionCode.SignedSupport.no_common_bubble_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:02:56.416943+00:00
-- url     : https://prove2.me/submissions/b0c0ef70-3f07-4708-b454-f6f294f74b47

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_source_vertices
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_target_vertices

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L)
    (hn : g ∈ windowSet (F.path b false) L (F.extra b false))
    (hp : g ∈ windowSet (F.path b true) L (F.extra b true)) : False := by
  obtain ⟨i, hi⟩ := hn
  obtain ⟨j, hj⟩ := hp
  have hiBound := i.isLt
  have hjBound := j.isLt
  have he : gram (F.path b false) L i.val = gram (F.path b true) L j.val :=
    hi.trans hj.symm
  have hs := H.endpoints b i.val j.val (by omega) (by omega)
    (gram_eq_source_vertices F L b b false true i.val j.val he)
  have hi0 : i.val = 0 := by
    rcases hs with ⟨hi0, hj0⟩ | ⟨hiEnd, hjEnd⟩
    · exact hi0
    · omega
  have hj0 : j.val = 0 := by
    rcases hs with ⟨hi0, hj0⟩ | ⟨hiEnd, hjEnd⟩
    · exact hj0
    · omega
  have ht := H.endpoints b (i.val + 1) (j.val + 1) (by omega) (by omega)
    (gram_eq_target_vertices F L b b false true i.val j.val he)
  rcases ht with ⟨hzero, _⟩ | ⟨hEndN, hEndP⟩
  · omega
  · exact H.differentLengths b (by omega)
end DeletionCode.SignedSupport
