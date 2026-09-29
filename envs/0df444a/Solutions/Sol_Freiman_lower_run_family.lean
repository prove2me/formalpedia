-- Prove2me | solution 1 for Freiman.lower_run_family
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:28.402987+00:00
-- url     : https://prove2.me/submissions/f4961531-8918-4496-a46e-ce0a4f2d6ef7

import Theorems.Thm_Freiman_lower_run_goodness
import Theorems.Thm_Freiman_lower_run_connected_gluing
import Theorems.Thm_Freiman_lower_run_parity_contacts
import Theorems.Thm_Freiman_lower_run_endpoint_limits
import Theorems.Thm_Freiman_lower_repeated3_model
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerRunFamily p := by
  have hg := lower_run_goodness t p hs hr
  exact ⟨hg, lower_run_connected_gluing p hg (lower_run_parity_contacts t p hs hr)
    (lower_run_endpoint_limits t p hs hr), lower_repeated3_model t p hs hr⟩
