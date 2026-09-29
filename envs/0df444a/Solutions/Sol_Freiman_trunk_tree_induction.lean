-- Prove2me | solution 1 for Freiman.trunk_tree_induction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:09.523308+00:00
-- url     : https://prove2.me/submissions/89606f1b-bf21-4891-96ad-d1c12d9a20cc

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_tree_induction_with_boundary
import Theorems.Thm_Freiman_trunk_boundary_exclusion

open Freiman

theorem solution (C : TrunkCatalog) (hw : trunkAllWitnesses C)
    (he : ∀ w : TrunkWitness, trunkWitnessValid C w → TrunkWitnessExclusion C w)
    (hs : ∀ (R : CertRectangle) (axis : Bool), certRectangleValid R → ∀ r s : ℝ, certRectangleMem R r s →
      (certRectangleValid (trunkRectangleHalf R axis false) ∧ certRectangleValid (trunkRectangleHalf R axis true)) ∧
      (certRectangleMem (trunkRectangleHalf R axis false) r s ∨ certRectangleMem (trunkRectangleHalf R axis true) r s)) :
    TrunkTreeSound C := by
  exact trunk_tree_induction_with_boundary C hw he hs trunk_boundary_exclusion
