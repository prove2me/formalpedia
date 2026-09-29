-- Prove2me | solution 1 for Freiman.section14_record_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:18:37.428457+00:00
-- url     : https://prove2.me/submissions/899b67f4-4fad-4e09-9081-9888dfdc3c3d

import Theorems.Thm_Freiman_section14_record_from_pair
import Theorems.Thm_Freiman_cert_witness_excludes
import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem solution : ∀ (C : Section14Catalog) (si : ℕ) (rec : Section14Record), section14RecordValid C si rec → section14RecordSound C si rec := by
  exact section14_record_from_pair cert_witness_excludes
