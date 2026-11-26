-- Prove2me | solution 1 for FourierJacobi.Analysis.collisionProbability_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:38.273282+00:00
-- url     : https://prove2.me/submissions/ff4549f2-7b19-487b-9e94-dbc8ffd20318

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (c : ℕ) :
    collisionProbability q (c + 1) = q⁻¹ * (q⁻¹) ^ c := by
  unfold collisionProbability
  rw [if_neg (by omega), zpow_neg, zpow_natCast]
  simp only [pow_succ, mul_inv_rev, inv_pow]
end FourierJacobi.Analysis
