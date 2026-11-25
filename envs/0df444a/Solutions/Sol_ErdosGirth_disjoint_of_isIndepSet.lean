-- Prove2me | solution 1 for ErdosGirth.disjoint_of_isIndepSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:09.645666+00:00
-- url     : https://prove2.me/submissions/d6199f6c-13a4-42a7-a73a-109817470a22

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {m : ℕ} {S : Finset (Sym2 (Fin m))} {T : Finset (Fin m)}
    (h : (gr S).IsIndepSet (T : Set (Fin m))) : Disjoint (edgesIn T) S := by
  rw [Finset.disjoint_left]
  intro e he heS
  simp only [edgesIn, mem_image, mem_offDiag] at he
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩ := he
  exact h (mem_coe.mpr ha) (mem_coe.mpr hb) hab ((fromEdgeSet_adj _).mpr ⟨heS, hab⟩)
end ErdosGirth
