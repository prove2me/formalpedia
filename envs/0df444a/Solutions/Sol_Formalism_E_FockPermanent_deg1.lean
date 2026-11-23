-- Prove2me | solution 1 for Formalism.E.FockPermanent.deg1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:26.092533+00:00
-- url     : https://prove2.me/submissions/690fe137-d0c6-43da-8a8d-11b286a53fc9

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix MvPolynomial
noncomputable section
open Formalism Formalism.E
open Formalism.E.FockPermanent
variable {R τ : Type*} [CommRing R]
namespace Formalism.E.FockPermanent
theorem _root_.solution (d : τ →₀ ℕ) (h : d.degree = 1) : ∃ k, d = Finsupp.single k 1 := by
  classical
  have hc : Multiset.card (Finsupp.toMultiset d) = 1 := by
    rw [Finsupp.card_toMultiset, Finsupp.sum]; exact h
  obtain ⟨k, hk⟩ := Multiset.card_eq_one.mp hc
  refine ⟨k, ?_⟩
  calc d = Multiset.toFinsupp (Finsupp.toMultiset d) := (Finsupp.toMultiset_toFinsupp d).symm
    _ = _ := by rw [hk]; simp
end Formalism.E.FockPermanent
