-- Prove2me | solution 1 for Freiman.trunk_boundary_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:32:05.902782+00:00
-- url     : https://prove2.me/submissions/427f66f7-7e22-44a4-839b-5cee5a7f9610

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem solution :
    trunkBoundaryCertificateValid := by
  unfold trunkBoundaryCertificateValid certThresholdDataValid
  decide +kernel
