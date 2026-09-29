-- Prove2me | solution 1 for Freiman.trunk_normal_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:37.870711+00:00
-- url     : https://prove2.me/submissions/9803c116-a268-4097-b985-dd125eccbcc8

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_normal_use_valid
import Theorems.Thm_Freiman_cert_witness_excludes

open Freiman

theorem solution (C : TrunkCatalog) (w : TrunkWitness)
    (hw : trunkWitnessValid C w) (hz : w.diagonal = 0) :
    TrunkWitnessExclusion C w := by
  intro l u hu r s q hm _
  exact cert_witness_excludes _ (trunk_normal_use_valid C w hw hz l u hu) r s q hm
