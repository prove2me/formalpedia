-- Prove2me | solution 1 for FourierJacobi.Analysis.dampedRational_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:09.153729+00:00
-- url     : https://prove2.me/submissions/3fc56ee7-848a-4c46-9415-3bd396849616

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t : ℝ) (a b d : ℂ) :
    dampedRational t a b d 1 = finiteCore (t : ℂ) a b d := by
  simp only [dampedRational, finiteCore, Complex.ofReal_one, one_mul]
end FourierJacobi.Analysis
