-- Prove2me | solution 1 for FD1D.levelSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:11.726186+00:00
-- url     : https://prove2.me/submissions/01656744-2696-4582-a1a4-2658b4e01f4a

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_sum_children

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution {A : Type*} [AddCommMonoid A]
    (f : ∀ d, DyadicNode d → A) (d : ℕ) :
    levelSum f (d + 1) =
      ∑ v, (f (d + 1) (leftChild v) + f (d + 1) (rightChild v)) := by
  exact sum_children d (f (d + 1))
end FD1D
