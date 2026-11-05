-- Prove2me | solution 1 for GaleShapley1962.Admissions.theorem_2
-- status  : ACCEPTED   (disprove)
-- author  : @frknbls
-- created : 2026-11-04T13:45:39.815636+00:00
-- url     : https://prove2.me/submissions/58bf3b6c-2175-454b-8443-cf56fed1767e

import Definitions.Def_GaleShapley1962_Admissions_Procedure

namespace GaleShapley1962.Admissions

def s0Mkt : Market 2 1 where
  applicantList := fun _ => [0]
  collegeList := fun _ => [0, 1]
  applicant_nodup := by intro a; decide
  college_nodup := by intro c; decide
  quota := fun _ => 1

def s0Mu : Assignment 2 1 := fun a => if a = 1 then some 0 else none

theorem s0_da1 : s0Mkt.deferredAcceptance 1 = none := by
  unfold Market.deferredAcceptance Market.fuel
  decide +kernel

theorem s0_feas : s0Mkt.Feasible s0Mu := by
  unfold Market.Feasible
  decide +kernel

theorem s0_stable : s0Mkt.PrintedStable s0Mu := by
  unfold Market.PrintedStable
  decide +kernel

end GaleShapley1962.Admissions

theorem _root_.solution : ¬ (∀ {n m : ℕ} (M : GaleShapley1962.Admissions.Market n m),
    M.Feasible M.deferredAcceptance ∧
    M.PrintedStable M.deferredAcceptance ∧
    ∀ μ : GaleShapley1962.Admissions.Assignment n m, M.Feasible μ → M.PrintedStable μ →
      ∀ a : Fin n, M.WeaklyPrefers a (M.deferredAcceptance a) (μ a)) := by
  intro h
  have h3 := (h GaleShapley1962.Admissions.s0Mkt).2.2 _ GaleShapley1962.Admissions.s0_feas
    GaleShapley1962.Admissions.s0_stable 1
  rw [GaleShapley1962.Admissions.s0_da1] at h3
  unfold GaleShapley1962.Admissions.Market.WeaklyPrefers at h3
  rcases h3 with h3 | ⟨c, hc, _⟩
  · revert h3; decide +kernel
  · cases hc
