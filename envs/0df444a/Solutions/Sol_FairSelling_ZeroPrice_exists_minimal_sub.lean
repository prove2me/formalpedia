-- Prove2me | solution 1 for FairSelling.ZeroPrice.exists_minimal_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:27.041438+00:00
-- url     : https://prove2.me/submissions/616a43c5-b4e0-4003-8e33-1a052e44da9c

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ZeroPrice
theorem _root_.solution {α : Type*} [DecidableEq α] (P : Finset α → Prop) :
    ∀ (B : Finset α), P B → ∃ C ⊆ B, P C ∧ ∀ g ∈ C, ¬ P (C.erase g) := by
  intro B
  induction B using Finset.strongInduction with
  | _ B ih =>
    intro hB
    by_cases h : ∃ g ∈ B, P (B.erase g)
    · obtain ⟨g, hg, hPg⟩ := h
      obtain ⟨C, hCsub, hC, hCmin⟩ := ih (B.erase g) (Finset.erase_ssubset hg) hPg
      exact ⟨C, hCsub.trans (Finset.erase_subset _ _), hC, hCmin⟩
    · push_neg at h
      exact ⟨B, Finset.Subset.refl _, hB, h⟩
end FairSelling.ZeroPrice
