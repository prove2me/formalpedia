-- Prove2me | solution 1 for Freiman.late_proof_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:15:21.003385+00:00
-- url     : https://prove2.me/submissions/edd306d7-af40-4138-8e07-999b8867e57e

import Theorems.Thm_Freiman_late_proof_from_witness
import Theorems.Thm_Freiman_cert_witness_excludes
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : ∀ C : LateCatalog, lateAllWitnesses C → lateProofSound C := by
  exact late_proof_from_witness cert_witness_excludes
