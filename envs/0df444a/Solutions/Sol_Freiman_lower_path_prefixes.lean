-- Prove2me | solution 1 for Freiman.lower_path_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:03:31.816598+00:00
-- url     : https://prove2.me/submissions/2a5d232b-ce74-4ebd-ac23-528d6e959445

import Theorems.Thm_Freiman_lower_physical_prefix_transfer
import Theorems.Thm_Freiman_lower_selected_words
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    (∀ n, lowerAdmissible (lowerPhysicalPath h n)) ∧
    (∀ n, lowerExtends (lowerPhysicalPath h n) (lowerPhysicalPath h (n+1))) ∧
    (∀ n, lowerPrefixSize (lowerPhysicalPath h n) < lowerPrefixSize (lowerPhysicalPath h (n+1))) := by
  exact lower_physical_prefix_transfer lower_selected_words t h hh
