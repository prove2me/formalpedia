-- Prove2me | solution 1 for ErdosPosa.deg_restr_compl_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:17.656624+00:00
-- url     : https://prove2.me/submissions/9418ee5d-1662-4be2-833a-2894a845e5a5

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable {H₀ : SimpleGraph V} {T : Set V}
namespace ErdosPosa
theorem _root_.solution {v : V} (hv : v ∈ T) : deg (restr H₀ Tᶜ) v = 0 := by
  rw [deg, show (restr H₀ Tᶜ).neighborSet v = ∅ from ?_, Set.ncard_empty]
  ext w
  simp only [mem_neighborSet, restr_adj, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h, -⟩; exact h hv
end ErdosPosa
