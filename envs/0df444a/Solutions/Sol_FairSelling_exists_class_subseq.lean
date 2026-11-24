-- Prove2me | solution 1 for FairSelling.exists_class_subseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:05.303066+00:00
-- url     : https://prove2.me/submissions/19ce2a17-fa82-4345-aa3d-6026d29e9768

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven

set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (o : ℕ → Outcome G n) :
    ∃ (S : Finset G) (A : Fin n → Finset G) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ k, (o (φ k)).sold = S) ∧ (∀ k, (o (φ k)).kept = A) := by
  classical
  have hfreq : ∃ c : Finset G × (Fin n → Finset G),
      ∃ᶠ k in atTop, ((o k).sold, (o k).kept) = c := by
    by_contra h
    push_neg at h
    have h' : ∀ c : Finset G × (Fin n → Finset G),
        ∀ᶠ k in atTop, ((o k).sold, (o k).kept) ≠ c := by
      intro c
      simpa [Filter.not_frequently] using h c
    have h'' : ∀ᶠ k in atTop, ∀ c : Finset G × (Fin n → Finset G),
        ((o k).sold, (o k).kept) ≠ c := Filter.eventually_all.2 h'
    obtain ⟨k, hk⟩ := h''.exists
    exact hk _ rfl
  obtain ⟨c, hc⟩ := hfreq
  obtain ⟨φ, hφ, hφc⟩ := Filter.extraction_of_frequently_atTop hc
  refine ⟨c.1, c.2, φ, hφ, fun k => ?_, fun k => ?_⟩
  · exact congrArg Prod.fst (hφc k)
  · exact congrArg Prod.snd (hφc k)
end FairSelling
