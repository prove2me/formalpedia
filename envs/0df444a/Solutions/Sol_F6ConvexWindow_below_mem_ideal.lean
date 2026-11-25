-- Prove2me | solution 1 for F6ConvexWindow.below_mem_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:34:04.449687+00:00
-- url     : https://prove2.me/submissions/06da11bb-4911-4307-b88a-c3b6aaa83616

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.mem_ideal

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {T : Finset V} {x : V} (h : Below T x) : x ∈ ideal T := by
  classical
  obtain ⟨t, ht⟩ := card_pos.mp (show 0 < (T.filter (fun t => x < t)).card by
    unfold Below at h
    omega)
  obtain ⟨ht, hxt⟩ := mem_filter.mp ht
  exact mem_ideal.mpr ⟨t, ht, hxt.le⟩
end F6ConvexWindow
