-- Prove2me | solution 1 for FourierJacobi.Analysis.i2Case8c_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:52.617973+00:00
-- url     : https://prove2.me/submissions/149a3572-2300-4998-b410-24d26b486099

import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Tactic.FinCases
import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Theorems.Thm_FourierJacobi_Valuations_tableTwo_correct


set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (p : I2SpatialRow 21) (c : ℕ) (hc : c = 1) :
    cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = (2, -p.val.1-p.val.2.1-1) := by
  have hp := p.property
  change p.val.1 ≤ 0 ∧ p.val.2.1 < -1 ∧ p.val.2.1 ≤ p.val.2.2 ∧ 2*p.val.2.2 = p.val.2.1-2 at hp
  rw [← tableTwo_correct _ _ _ _ (by omega)]
  unfold tableTwo collisionRows
  split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega
end FourierJacobi.Analysis
