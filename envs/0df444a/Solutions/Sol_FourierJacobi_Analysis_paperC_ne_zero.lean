-- Prove2me | solution 1 for FourierJacobi.Analysis.paperC_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:16.877626+00:00
-- url     : https://prove2.me/submissions/ebdb53e4-467f-4a6b-8adb-225f7a6ed873

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_FourierJacobi_Algebra_poincare_coe_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_paperC_eq_poincare


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) : paperC q ≠ 0 := by
  rw [paperC_eq_poincare q (by linarith)]
  exact poincare_coe_ne_zero _
end FourierJacobi.Analysis
