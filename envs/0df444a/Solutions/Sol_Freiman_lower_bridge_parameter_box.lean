-- Prove2me | solution 1 for Freiman.lower_bridge_parameter_box
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:08:17.250982+00:00
-- url     : https://prove2.me/submissions/4b4562a6-019e-43bb-920f-6afcf495feac

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_initial_parameter_box

open Freiman

theorem solution (n k : ℕ) : certRectangleMem lowerBridgeRectangle (lowerInitialX n) (lowerInitialY k) := by
  have h := Freiman.lower_initial_parameter_box n k 0
  simpa [certRectangleMem, lowerBridgeRectangle] using (show (0:ℝ) ≤ lowerInitialX n ∧ lowerInitialX n ≤ (1/85:ℝ) ∧ (0:ℝ) ≤ lowerInitialY k ∧ lowerInitialY k ≤ (1/3:ℝ) from ⟨h.1.1,h.1.2,h.2.1.1,h.2.1.2⟩)
