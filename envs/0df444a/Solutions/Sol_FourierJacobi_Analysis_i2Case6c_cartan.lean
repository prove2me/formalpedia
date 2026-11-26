-- Prove2me | solution 1 for FourierJacobi.Analysis.i2Case6c_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:31.506897+00:00
-- url     : https://prove2.me/submissions/28662a1e-05e5-4500-b0fa-b672af4a3a0d

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
theorem _root_.solution (p : I2SpatialRow 15) (c : ℕ) :
    cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = (4, -p.val.1-2) := by
  have hp := p.property
  change p.val.1 ≤ -2 ∧ 0 ≤ p.val.2.1 ∧ 0 ≤ p.val.2.2 at hp
  rw [← tableTwo_correct _ _ _ _ (by omega)]
  unfold tableTwo collisionRows
  split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega
end FourierJacobi.Analysis
