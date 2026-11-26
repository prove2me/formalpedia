-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_dampedRational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:14.166355+00:00
-- url     : https://prove2.me/submissions/1a99983a-338a-4167-974f-9d139883ed8b

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Theorems.Thm_FourierJacobi_Analysis_dampedRational_one
import Theorems.Thm_FourierJacobi_Analysis_continuousAt_dampedRational
import Theorems.Thm_FourierJacobi_Algebra_finiteCore_eq_closedCore
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.dampedRational_one

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t : ℝ) (a b d : ℂ)
    (h : FiniteRegular (t : ℂ) a b d) :
    Tendsto (dampedRational t a b d) (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (closedCore (t : ℂ) a b d)) := by
  have hc := (continuousAt_dampedRational t a b d h).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioo (0 : ℝ) 1))
  simpa only [dampedRational_one, finiteCore_eq_closedCore _ _ _ _ h] using hc
end FourierJacobi.Analysis
