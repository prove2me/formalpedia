-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:54:35.077974+00:00
-- url     : https://prove2.me/submissions/a4bce7e7-a3ee-46c2-8687-9bef77c999dc

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP
import Definitions.Def_PuhaWardFluid_Limit_Paths
import Theorems.Thm_ForkJoinCtrl_Tracking_lemma_1_part_3

open scoped NNReal
open ForkJoinCtrl.Tracking

theorem solution (N : Network) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ (b : ℝ≥0 → LPParam N) (x : ℝ≥0 → LPVar N),
      PuhaWardFluid.Limit.IsCadlag b →
      PuhaWardFluid.Limit.IsCadlag (fun t => (x t).y) →
      PuhaWardFluid.Limit.IsCadlag (fun t => (x t).q) →
      (∀ t, (b t).Nonneg) → (∀ t, QPOpt N (b t) (x t)) →
      ∀ s t : ℝ≥0, ∀ i j, N.P i j = true →
        |(x s).q i j - (x t).q i j| ≤ C2 * ‖b s - b t‖ := by
  obtain ⟨_, C2, hC2, hlip⟩ := ForkJoinCtrl.Tracking.lemma_1_part_3 N
  refine ⟨C2, hC2, ?_⟩
  intro b x _ _ _ hb hx s t i j hij
  exact hlip (b s) (b t) (x s) (x t) (hb s) (hb t) (hx s) (hx t) i j hij
