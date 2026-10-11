-- Prove2me | solution 1 for BlackScholesModel.put_call_parity_fwd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:07:58.049613+00:00
-- url     : https://prove2.me/submissions/fcfd2289-183f-4017-b597-7646959f7dae

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (D F K σ τ : ℝ) :
    callPriceFwd D F K σ τ - putPriceFwd D F K σ τ = D * (F - K) := by
  simp only [callPriceFwd, putPriceFwd, stdNormalCDF_neg]
  ring
