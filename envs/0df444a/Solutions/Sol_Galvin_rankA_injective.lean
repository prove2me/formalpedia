-- Prove2me | solution 1 for Galvin.rankA_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:57:02.976979+00:00
-- url     : https://prove2.me/submissions/4cbcb582-6271-4c52-822c-67c4ee2ea2bb

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
    {idx : V → ℕ} (hidx : Function.Injective idx) (m : V) :
    Function.Injective (rankA c φ idx m) := by
  intro w w' hww
  unfold rankA at hww
  split_ifs at hww with h h'
  · have := eq_of_colour_eq c φ (Fin.ext hww)
      (Or.inl (h.choose_spec.1.trans h'.choose_spec.1.symm))
    rw [← h.choose_spec.2, ← h'.choose_spec.2, this]
  · have := (φ h.choose).isLt; omega
  · rename_i h₂; have := (φ h₂.choose).isLt; omega
  · exact hidx (by omega)
end Galvin
