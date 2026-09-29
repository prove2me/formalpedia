-- Prove2me | solution 1 for Freiman.gap_maximum_admissible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:41:18.483698+00:00
-- url     : https://prove2.me/submissions/aaa1accd-4de9-4437-bbd1-42a3ec754292

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_maximum_forbidden
import Theorems.Thm_Freiman_gap_maximum_334
import Theorems.Thm_Freiman_gap_capped_digits

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) : gapMaximumAdmissible a := by
  have hf := gap_maximum_forbidden a hc
  exact ⟨hf,gap_maximum_334 a (gap_capped_digits a hc) hf⟩
