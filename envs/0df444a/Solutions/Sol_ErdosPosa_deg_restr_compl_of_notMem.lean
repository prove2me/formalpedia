-- Prove2me | solution 1 for ErdosPosa.deg_restr_compl_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:20.983532+00:00
-- url     : https://prove2.me/submissions/b6f1acee-3f96-4dc9-8f04-5e2eed97473c

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
theorem _root_.solution {v : V} (hv : v ∉ T) :
    deg (restr H₀ Tᶜ) v = (H₀.neighborSet v \ T).ncard := by
  unfold deg
  rw [show (restr H₀ Tᶜ).neighborSet v = H₀.neighborSet v \ T from ?_]
  ext w
  simp only [mem_neighborSet, restr_adj, Set.mem_compl_iff, Set.mem_sdiff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hv, h.2⟩⟩
end ErdosPosa
