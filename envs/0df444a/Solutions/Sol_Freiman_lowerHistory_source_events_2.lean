-- Prove2me | solution 2 for Freiman.lowerHistory_source_events
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:28:19.064322+00:00
-- url     : https://prove2.me/submissions/e7f248af-2f55-49c9-a973-83b82926636c

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_reached_base
import Theorems.Thm_Freiman_lowerHistory_reached_goodness
import Theorems.Thm_Freiman_lowerHistory_reached_choices
import Theorems.Thm_Freiman_lowerHistory_reached_normalizations
import Theorems.Thm_Freiman_lowerHistory_reached_final
import Theorems.Thm_Freiman_lowerHistory_goodness_semantics
import Theorems.Thm_Freiman_lowerHistory_pull_value
import Theorems.Thm_Freiman_lowerHistory_source_choices
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lower_forced_reflections
import Theorems.Thm_Freiman_lower_entry_family_domain

open Freiman

theorem solution : ∀ (t : ℝ) (h : ℕ → LowerPair) (n : ℕ),
    lowerHistory t h n → ∀ (base : LowerPair) (p : LowerHistoryPath),
      lowerHistoryStructural p → lowerHistoryReached t h n base p →
      lowerHistoryHazard p.row (h n) → LowerHistorySourceEvents base p := by
  intro t h n hh base p hp hr haz
  have hfamily : ∀ (f : LowerInitialFamily) (a k v : ℕ),
      lowerEntryDomain (lowerNormalize (lowerFamilyPair f a k v)) := by
    intro f a k v
    exact lower_entry_family_domain f a k v
  have hg : LowerHistoryGoodnessLaw := lowerHistory_goodness_semantics
  have hpull : LowerHistoryPullLaw := lowerHistory_pull_value
  have hc : LowerHistoryChoiceLaw := lowerHistory_source_choices
  have hwidth : LowerHistoryWidthLaw := by
    intro b w
    exact lowerHistory_width_threshold b w
  have hf : ∀ (q : LowerPair), lowerGood q → lowerParameterBox q →
      let z := lowerNormalize q
      lowerWidth (z.1 ++ [2]) < lowerWidth z.2 ∧
      lowerWidth (z.1 ++ [3]) < lowerWidth z.2 ∧
      lowerWidth (z.1 ++ [1,1]) < lowerWidth z.2 ∧
      lowerWidth (z.2 ++ [1]) < lowerWidth z.1 := lower_forced_reflections
  exact {
    baseEvent := lowerHistory_reached_base hfamily hg t h n hh base p hp hr,
    goodEvents := lowerHistory_reached_goodness hg hpull t h n hh base p hp hr,
    choiceEvents := lowerHistory_reached_choices hc hpull t h n hh base p hp hr,
    normalizationEvents := lowerHistory_reached_normalizations hf hwidth t h n hh base p hp hr,
    finalEvent := lowerHistory_reached_final hpull t h n hh base p hp hr haz }
