-- Prove2me | solution 1 for FourierJacobi.Analysis.collisionWeight_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:11.34013+00:00
-- url     : https://prove2.me/submissions/34924321-1652-4c3e-81b5-ab4c44319baf

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
theorem _root_.solution (q : ℂ) (r j h : ℤ) (c : ℕ) :
    ‖collisionWeight q r j h c‖ ≤ depthMajorant q c := by
  unfold collisionWeight depthMajorant
  split_ifs <;> simp
end FourierJacobi.Analysis
