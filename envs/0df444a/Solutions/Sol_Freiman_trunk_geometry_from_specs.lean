-- Prove2me | solution 1 for Freiman.trunk_geometry_from_specs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:30.354496+00:00
-- url     : https://prove2.me/submissions/82073c59-6ebb-4850-8620-ce97c3518721

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_nonempty_from_specs
import Theorems.Thm_Freiman_trunk_goodness_from_specs
import Theorems.Thm_Freiman_trunk_contacts_from_specs
import Theorems.Thm_Freiman_trunk_anchors_from_specs

open Freiman

theorem solution (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    TrunkGeometry p (trunkPlanAt (trunkCatalog.states k) pi) := by
  exact ⟨trunk_nonempty_from_specs p k pi par hm hs,
    trunk_goodness_from_specs p k pi par hm hs,
    trunk_contacts_from_specs p k pi par hm hs,
    (trunk_anchors_from_specs p k pi par hm hs).1,
    (trunk_anchors_from_specs p k pi par hm hs).2⟩
