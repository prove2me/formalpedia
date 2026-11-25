-- Prove2me | solution 1 for GallaiRoy.exists_orientation_of_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:16:11.286515+00:00
-- url     : https://prove2.me/submissions/83b723aa-02b8-4a04-a5cf-67fd42a849bb

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiRoy
variable {V : Type*}
namespace GallaiRoy
theorem _root_.solution (G : SimpleGraph V) (k : ℕ) (h : G.Colorable k) :
    ∃ o : V → V → Prop, IsOrientation G o ∧
      ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k := by
  obtain ⟨c⟩ := h
  refine ⟨fun u v => G.Adj u v ∧ c u < c v, ⟨fun u v huv => ?_, fun u v h => h.1⟩, ?_⟩
  · rcases lt_or_gt_of_ne (c.valid huv) with h | h
    · exact .inl ⟨huv, h⟩
    · exact .inr ⟨huv.symm, h⟩
  · intro m f hf
    cases m with
    | zero => exact Nat.zero_le _
    | succ n =>
    have hmono : StrictMono (fun i : Fin (n + 1) => c (f i)) := by
      refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      have := hf.2 i.1 (by omega)
      exact this.2
    simpa using Fintype.card_le_of_injective _ hmono.injective
end GallaiRoy
