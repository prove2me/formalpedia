-- Prove2me | solution 1 for Freiman.trunk_boundary_polynomial_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:38:19.878217+00:00
-- url     : https://prove2.me/submissions/73ca7fb1-320e-460b-a6af-b131610b8cae

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_boundary_from_factor
import Theorems.Thm_Freiman_trunk_diagonal_factor
import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_field_scale

open Freiman

theorem solution (hc : trunkBoundaryCertificateValid) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s)
    (hp : certPolyEval trunkBoundaryPolynomial r s ≤ 0) :
    r = s := by
  exact trunk_boundary_from_factor trunk_diagonal_factor cert_field_lower_bound cert_field_scale hc r s hr hs hrs hp
