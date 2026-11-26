-- Prove2me | solution 1 for GallaiEdmondsTheorem.maximumMatching_structure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:28.464426+00:00
-- url     : https://prove2.me/submissions/033360b4-1146-47b5-ae4f-eb4e45e0a0fa

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_GallaiEdmonds_maximumMatching_structure


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmondsTheorem
theorem _root_.solution [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    (∀ v ∈ setC G, ∃ w ∈ setC G, M.Adj v w) ∧
    (∀ a ∈ setA G, ∃ u ∈ setD G, M.Adj a u) ∧
    (∀ a ∈ setA G, ∀ a' ∈ setA G, ∀ u u' : ↥(setD G), a ≠ a' → M.Adj a u → M.Adj a' u' →
      (G.induce (setD G)).connectedComponentMk u ≠
        (G.induce (setD G)).connectedComponentMk u') ∧
    (∀ c : (G.induce (setD G)).ConnectedComponent, ∀ v ∈ compSet G c, ∀ w ∈ compSet G c,
      v ≠ w → (∃ x ∈ compSet G c, M.Adj v x) ∨ (∃ x ∈ compSet G c, M.Adj w x)) :=
  GallaiEdmonds.maximumMatching_structure G hM
end GallaiEdmondsTheorem
