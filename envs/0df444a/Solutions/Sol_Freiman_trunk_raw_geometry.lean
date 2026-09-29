-- Prove2me | solution 1 for Freiman.trunk_raw_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:49.596136+00:00
-- url     : https://prove2.me/submissions/110bc24e-db01-4909-8e11-af0ad5cade43

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_geometry_from_specs
import Theorems.Thm_Freiman_trunk_specs_sound

open Freiman

theorem solution :
    TrunkGeometryLaw := by
  intro p k pi par hm
  exact trunk_geometry_from_specs p k pi par hm (trunk_specs_sound p k pi par hm)
