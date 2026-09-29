-- Prove2me | solution 1 for Freiman.trunk_endpoint_strict_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:30.24253+00:00
-- url     : https://prove2.me/submissions/533f38f5-21d6-4c05-af8f-0044d49b788e

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_endpoint_strict_equal
import Theorems.Thm_Freiman_trunk_endpoint_strict_mixed

open Freiman

theorem solution (p : LowerPair) :
    lowerEndpoint p false < lowerEndpoint p true := by
  by_cases hp : p.1.length % 2 = p.2.length % 2
  · exact trunk_endpoint_strict_equal p hp
  · exact trunk_endpoint_strict_mixed p hp
