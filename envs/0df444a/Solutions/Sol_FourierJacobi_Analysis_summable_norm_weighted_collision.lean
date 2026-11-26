-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_weighted_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:46.657798+00:00
-- url     : https://prove2.me/submissions/7250930a-9ba9-4308-9489-7cdb1a12887d

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_depthMajorant_nonneg
import Theorems.Thm_FourierJacobi_Analysis_summable_depthMajorant
import Theorems.Thm_FourierJacobi_Analysis_collisionWeight_norm_le
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution {ι : Type*} (q : ℂ) (r : ℤ)
    (j h : ι → ℤ) (f : ι → ℂ) (hq : ‖q⁻¹‖ < 1)
    (hf : Summable (fun p => ‖f p‖)) :
    Summable (fun p : ι × ℕ => ‖f p.1 * collisionWeight q r (j p.1) (h p.1) p.2‖) := by
  have hm := hf.mul_of_nonneg (summable_depthMajorant q hq)
    (fun p => norm_nonneg (f p)) (depthMajorant_nonneg q)
  apply hm.of_norm_bounded
  intro p
  simp only [norm_norm, norm_mul]
  exact mul_le_mul_of_nonneg_left (collisionWeight_norm_le q r (j p.1) (h p.1) p.2)
    (norm_nonneg _)
end FourierJacobi.Analysis
