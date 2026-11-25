-- Prove2me | solution 1 for Galvin.rankB_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:57:47.218672+00:00
-- url     : https://prove2.me/submissions/a5555ce7-3567-4344-af40-84377152edfb

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_eq_of_colour_eq

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {idx : V → ℕ} (hidx : Function.Injective idx) (w : V) :
    Function.Injective (rankB c φ idx w) := by
  intro m m' hmm
  unfold rankB at hmm
  split_ifs at hmm with h h'
  · have h1 := (φ h.choose).isLt
    have h2 := (φ h'.choose).isLt
    have := eq_of_colour_eq c φ (Fin.ext (by omega))
      (Or.inr (h.choose_spec.2.trans h'.choose_spec.2.symm))
    rw [← h.choose_spec.1, ← h'.choose_spec.1, this]
  · omega
  · omega
  · exact hidx (by omega)
end Galvin
