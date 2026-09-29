-- Prove2me | solution 1 for Freiman.late_decision_from_proofs
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:13:36.018593+00:00
-- url     : https://prove2.me/submissions/c1b6ee6e-bdfb-4bfc-bba9-87dc59d2f3e9

import Definitions.Def_Freiman_lateGeometry
import Theorems.Thm_Freiman_cert_witness_excludes
import Mathlib.Tactic.Linarith

open Freiman
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

private theorem scout_late_subrect_cover (R : CertRectangle) (axis : Bool) (r s : ℝ)
    (hm : certRectangleMem R r s) :
    certRectangleMem (lateSubrect R axis false) r s ∨
      certRectangleMem (lateSubrect R axis true) r s := by
  rcases hm with ⟨hr0, hr1, hs0, hs1⟩
  cases axis
  · by_cases h : r ≤ ((R.r0 + R.r1) / 2 : ℚ)
    · left
      simpa only [lateSubrect, Bool.false_eq_true, if_false, certRectangleMem]
        using And.intro hr0 (And.intro h (And.intro hs0 hs1))
    · right
      exact ⟨le_of_lt (lt_of_not_ge h), hr1, hs0, hs1⟩
  · by_cases h : s ≤ ((R.s0 + R.s1) / 2 : ℚ)
    · left
      exact ⟨hr0, hr1, hs0, h⟩
    · right
      exact ⟨hr0, hr1, le_of_lt (lt_of_not_ge h), hs1⟩

private theorem scout_late_complement (b : CertBound) (r s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q := by
  cases hl : b.lower <;> cases hs : b.strict <;>
    simp [certBoundHolds, lowerHistoryComplement, hl, hs]

private theorem scout_late_cons (b : CertBound) (bs : List CertBound) (r s q : ℝ)
    (hb : certBoundHolds b r s q) (hs : lateHolds bs r s q) :
    lateHolds (b :: bs) r s q := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  · exact hs x hx

theorem solution (hc : ∀ (b : CertBound) (r s q : ℝ), certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q) : ∀ (C : LateCatalog), lateProofSound C → ∀ right3 bs R tr,
    lateDecisionValid C right3 bs R tr → lateDecisionSound C right3 bs R := by
  intro C hp right3 bs R tr
  induction tr generalizing bs R with
  | cut id left right ihl ihr =>
      intro hv r s q hm hh
      by_cases hb : certBoundHolds (lateBound C id) r s q
      · exact ihl _ _ hv.2.1 r s q hm (scout_late_cons _ _ r s q hb hh)
      · exact ihr _ _ hv.2.2 r s q hm
          (scout_late_cons _ _ r s q ((hc _ r s q).2 hb) hh)
  | split axis left right ihl ihr =>
      intro hv r s q hm hh
      rcases scout_late_subrect_cover R axis r s hm with hmleft | hmright
      · exact ihl _ _ hv.1 r s q hmleft hh
      · exact ihr _ _ hv.2 r s q hmright hh
  | empty id =>
      intro hv r s q hm hh
      exact False.elim (hp 1500 bs R id hv r s q hm hh)
  | path id =>
      intro hv r s q hm hh
      obtain ⟨hidx, hright, _, hset, himps⟩ := hv
      refine ⟨id, hidx, hright, ?_⟩
      intro b hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hj' : j ∈ ((latePath C id).implications.map Prod.fst) := by
        apply List.mem_toFinset.mp
        rw [hset]
        exact List.mem_toFinset.mpr hj
      obtain ⟨imp, himp, hj⟩ := List.mem_map.mp hj'
      subst j
      have hvimp := himps imp himp
      cases he : imp.2 with
      | none =>
          rw [he] at hvimp
          exact hh _ hvimp
      | some proof =>
          rw [he] at hvimp
          by_contra hb
          exact hp 1500 _ R proof hvimp r s q hm
            (scout_late_cons _ _ r s q ((hc _ r s q).2 hb) hh)

#print axioms solution
