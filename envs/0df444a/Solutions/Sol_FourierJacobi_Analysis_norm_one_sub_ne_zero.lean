-- Prove2me | solution 1 for FourierJacobi.Analysis.norm_one_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:40.928822+00:00
-- url     : https://prove2.me/submissions/65706a4d-44df-4262-a9f6-58c6662d653c

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution {z : ℂ} (h : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro he
  have hz := congrArg norm (sub_eq_zero.mp he)
  rw [norm_one] at hz
  linarith
end FourierJacobi.Analysis
