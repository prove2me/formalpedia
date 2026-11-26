-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_collisionProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:24.045163+00:00
-- url     : https://prove2.me/submissions/81df249a-3d59-4939-8669-dc2241dd1463

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_collisionProbability_succ
import Theorems.Thm_FourierJacobi_Analysis_geometric_norm_summable
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionProbability q c‖) := by
  rw [← summable_nat_add_iff 1]
  simpa only [collisionProbability_succ, norm_mul, norm_pow] using
    (geometric_norm_summable q⁻¹ hq).mul_left ‖q⁻¹‖
end FourierJacobi.Analysis
