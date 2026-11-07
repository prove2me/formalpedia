-- Prove2me | solution 1 for FosterQueues.GIM1.theorem4_transient_iff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:26:25.783334+00:00
-- url     : https://prove2.me/submissions/00bd2a31-4b8a-4184-ae0e-9a477438f78e

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_FosterQueues_GIM1_Model
import Theorems.Thm_FosterQueues_MG1_theorem4_transience_criterion

open scoped ENNReal
open QueueingFundamentals.Foundations

theorem solution (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) :
    FosterQueues.MG1.IsTransient P ↔
      ∃ y : ℕ → ℝ, (∃ C : ℝ, ∀ i, |y i| ≤ C) ∧ (∃ i j, y i ≠ y j) ∧
        ∀ i, i ≠ 0 → HasSum (fun j => P.p i j * y j) (y i) :=
  FosterQueues.MG1.theorem4_transience_criterion P hirr hap
