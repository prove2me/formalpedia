-- Prove2me | solution 1 for Freiman.late_proof_from_witness
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:13:35.021168+00:00
-- url     : https://prove2.me/submissions/2bd1545c-aee1-4d89-bdea-cd75e5438e34

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

theorem solution (hex : ∀ w : CertWitness, certWitnessValid w → ∀ r s q : ℝ, certRectangleMem w.rectangle r s → ¬ (certBoundHolds w.lowerBound r s q ∧ certBoundHolds w.upperBound r s q)) : ∀ C : LateCatalog, lateAllWitnesses C → lateProofSound C := by
  intro C hw fuel
  induction fuel with
  | zero =>
      intro bs R id hv
      exact False.elim hv
  | succ fuel ih =>
      intro bs R id hv r s q hm hh
      rcases hv with ⟨_, hv⟩
      cases hn : C.proofs[id-1]?.getD (.pair 0) with
      | pair w =>
          rw [hn] at hv
          obtain ⟨hwidx, hl, hu, hR⟩ := hv
          apply hex (lateWitness C w) (hw w hwidx) r s q
          · simpa only [hR] using hm
          · exact ⟨hh _ hl, hh _ hu⟩
      | split axis left right =>
          rw [hn] at hv
          rcases scout_late_subrect_cover R axis r s hm with hmleft | hmright
          · exact ih bs _ left hv.1 r s q hmleft hh
          · exact ih bs _ right hv.2 r s q hmright hh

#print axioms solution
