-- Prove2me | solution 1 for ErdosPosa.Cyc.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:50.367024+00:00
-- url     : https://prove2.me/submissions/8ecb6cc4-1f32-41a2-a5da-0ea63692c160

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Theorems.Thm_ErdosPosa_cyc_iff

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
namespace Cyc
theorem _root_.solution {H : SimpleGraph V} {S : Set V} (h : Cyc H S) : ∃ x, x ∈ S := by
  rw [cyc_iff] at h
  obtain ⟨u, _, huv, _⟩ := h
  exact ⟨u, huv.2.1⟩
end Cyc
end ErdosPosa
