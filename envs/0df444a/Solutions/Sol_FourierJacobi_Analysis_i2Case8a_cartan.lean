-- Prove2me | solution 1 for FourierJacobi.Analysis.i2Case8a_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:48.893863+00:00
-- url     : https://prove2.me/submissions/807e440c-1fa3-4f12-a7d1-249b13b38434

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
theorem _root_.solution (p : I2SpatialRow 19) (c : ℕ) :
    cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = (4, -p.val.1-p.val.2.1-2) := by
  have hp := p.property
  change p.val.1 ≤ 0 ∧ p.val.2.1 < -1 ∧ p.val.2.1 ≤ p.val.2.2 ∧ p.val.2.1-1 ≤ 2*p.val.2.2 at hp
  rw [← tableTwo_correct _ _ _ _ (by omega)]
  unfold tableTwo collisionRows
  split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega
end FourierJacobi.Analysis
