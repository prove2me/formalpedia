-- Prove2me | solution 1 for C6BipartiteDomination.degreeTo_induce_eq_degreeWithinSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:08.437933+00:00
-- url     : https://prove2.me/submissions/f6349151-291c-4fa2-8788-c2e0f423fdfd

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (S : Finset V)
    (x : {v // v ∈ S}) :
    degreeTo (G.induce (S : Set V)) Finset.univ x =
      degreeWithinSet G S x.1 := by
  classical
  let H := G.induce (S : Set V)
  let A := Finset.univ.filter fun y : {v // v ∈ S} => H.Adj x y
  let f : {v // v ∈ S} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : A.map f = S.filter fun y => G.Adj x.1 y := by
    ext y
    simp [A, f, H, SimpleGraph.induce, and_comm]
  have hcard : A.card = (S.filter fun y => G.Adj x.1 y).card := by
    calc
      A.card = (A.map f).card := by simp
      _ = (S.filter fun y => G.Adj x.1 y).card := by rw [hmap]
  simpa [degreeTo, degreeWithinSet, A, H] using hcard
end C6BipartiteDomination
