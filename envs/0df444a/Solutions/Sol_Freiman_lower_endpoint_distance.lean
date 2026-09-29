-- Prove2me | solution 1 for Freiman.lower_endpoint_distance
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:13.784993+00:00
-- url     : https://prove2.me/submissions/120c447f-c347-4128-928a-2cf4869c88ef

import Theorems.Thm_Freiman_lower_endpoint_completion
import Theorems.Thm_Freiman_lower_cylinder_distance
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (p : LowerPair) (hp : lowerAdmissible p) (a : ℤ → ℕ+)
    (ha : LowerModel a) (hc : lowerCylinder p a) (upper : Bool) :
    |localValue a 0 - lowerEndpoint p upper| ≤ lowerCylinderError p := by
  have he := lower_endpoint_completion p hp upper
  have hd := lower_cylinder_distance p a
    (lowerPeriodicSequence (lowerEndpointWords p upper) [1,2]) hc he.2.1
  rwa [he.2.2] at hd
