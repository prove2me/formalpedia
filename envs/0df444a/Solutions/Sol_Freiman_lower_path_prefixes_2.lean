-- Prove2me | solution 2 for Freiman.lower_path_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:14:31.589646+00:00
-- url     : https://prove2.me/submissions/3644191b-d79c-4615-86ee-14e129238e20

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_selected_words
import Theorems.Thm_Freiman_lower_physical_prefix_transfer

open Freiman

-- `lower_physical_prefix_transfer` needs only the per-step word property, which is
-- exactly `lower_selected_words`.
theorem solution (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    (∀ n, lowerAdmissible (lowerPhysicalPath h n)) ∧
      (∀ n, lowerExtends (lowerPhysicalPath h n) (lowerPhysicalPath h (n + 1))) ∧
      (∀ n, lowerPrefixSize (lowerPhysicalPath h n) <
        lowerPrefixSize (lowerPhysicalPath h (n + 1))) :=
  lower_physical_prefix_transfer lower_selected_words t h hh
