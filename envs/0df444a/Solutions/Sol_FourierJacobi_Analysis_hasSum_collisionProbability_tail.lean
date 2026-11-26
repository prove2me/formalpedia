-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_collisionProbability_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:36.141848+00:00
-- url     : https://prove2.me/submissions/a760af3c-b092-4b64-a5d5-90591179b7f7

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_collisionProbability_succ
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (m : ℕ)
    (hq : ‖q⁻¹‖ < 1) :
    HasSum (fun c : ℕ => collisionProbability q (c + m + 1))
      ((q⁻¹) ^ (m + 1) * (1 - q⁻¹)⁻¹) := by
  have hg : HasSum (fun c : ℕ => (q⁻¹) ^ c) (1 - q⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hq
  have he : (fun c : ℕ => collisionProbability q (c + m + 1)) =
      (fun c : ℕ => (q⁻¹) ^ (m + 1) * (q⁻¹) ^ c) := by
    funext c
    rw [collisionProbability_succ]
    simp only [pow_add, pow_one]
    ring
  rw [he]
  exact hg.mul_left _
end FourierJacobi.Analysis
