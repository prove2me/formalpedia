-- Prove2me | solution 1 for Freiman.trunk_boundary_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:09.678968+00:00
-- url     : https://prove2.me/submissions/c3eb1fa4-d7c6-4a62-8df0-4091531c9efb

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_boundary_certificate
import Theorems.Thm_Freiman_trunk_boundary_polynomial_order
import Theorems.Thm_Freiman_trunk_boundary_q_control
import Theorems.Thm_Freiman_trunk_boundary_corner_contradiction

open Freiman

theorem solution (R : CertRectangle) (bs : List CertBound) (hb : trunkBoundaryBound R bs)
    (r s q : ℝ) (hm : certRectangleMem R r s) :
    ¬ trunkHolds bs r s q := by
  intro h
  have hr : 0 ≤ r := le_trans (by exact_mod_cast hb.1) hm.1
  have hs : 0 ≤ s := le_trans (by exact_mod_cast hb.2.1) hm.2.2.1
  have hrs : r ≤ s := le_trans hm.2.1 (le_trans (by exact_mod_cast hb.2.2.1.le) hm.2.2.1)
  have he := trunk_boundary_polynomial_order trunk_boundary_certificate r s hr hs hrs
    (trunk_boundary_q_control trunk_boundary_certificate R bs hb r s q hm h)
  exact trunk_boundary_corner_contradiction R bs hb r s q hm he h
