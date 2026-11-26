-- Prove2me | solution 1 for FourierJacobi.Analysis.residue_inverse_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:36.46181+00:00
-- url     : https://prove2.me/submissions/ff824690-20e7-46c7-9031-54c08d36feca

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) :
    ‖(q : ℂ)⁻¹‖ < 1 := by
  rw [norm_inv]
  have hqn : ‖(q : ℂ)‖ = q := by simp [abs_of_pos (show 0 < q by linarith)]
  rw [hqn]
  exact (inv_lt_one₀ (by linarith : 0 < q)).mpr hq
end FourierJacobi.Analysis
