-- Prove2me | solution 1 for FD1D.existsUnique_leafBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:12.610349+00:00
-- url     : https://prove2.me/submissions/0308d90f-ed47-417d-b5cc-56dc26b34ccf

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution {d L : ℕ} (hdL : d ≤ L)
    (w : DyadicNode L) :
    ∃! v : DyadicNode d, w ∈ leafBlock hdL v := by
  let x := (descendantsEquiv hdL).symm w
  refine ⟨x.1, ?_, ?_⟩
  · change w ∈ leafBlock hdL x.1
    rw [mem_leafBlock_iff]
    exact ⟨x.2, (descendantsEquiv hdL).apply_symm_apply w⟩
  · intro v hv
    rw [mem_leafBlock_iff] at hv
    obtain ⟨j, hj⟩ := hv
    have hp : (v, j) = x := by
      have hj' : descendantsEquiv hdL (v, j) = w := hj
      have hx : descendantsEquiv hdL x = w := by
        simp [x]
      apply (descendantsEquiv hdL).injective
      exact hj'.trans hx.symm
    exact congrArg Prod.fst hp
end FD1D
