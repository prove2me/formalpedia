-- Prove2me | solution 1 for FairSelling.price_zero_of_mem_bundle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:19.596027+00:00
-- url     : https://prove2.me/submissions/02898472-5635-4d5d-86a5-76aa6406002e

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}
namespace FairSelling
theorem _root_.solution (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (j : Fin n) {g : G} (hg : g ∈ A j) :
    p g = 0 := by
  have : g ∈ Finset.univ \ sellable := by
    rw [← hA.2]
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hg⟩
  exact hp0 g (Finset.mem_sdiff.mp this).2
end FairSelling
