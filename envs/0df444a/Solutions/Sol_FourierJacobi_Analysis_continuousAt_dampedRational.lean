-- Prove2me | solution 1 for FourierJacobi.Analysis.continuousAt_dampedRational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:17.16516+00:00
-- url     : https://prove2.me/submissions/f95c605c-8d81-4b81-9bde-e9d8ae5809e3

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Theorems.Thm_FourierJacobi_Analysis_continuousAt_damped_regionTerm

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t : ℝ) (a b d : ℂ)
    (h : FiniteRegular (t : ℂ) a b d) :
    ContinuousAt (dampedRational t a b d) 1 := by
  unfold dampedRational
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro i _
  apply Filter.Tendsto.const_mul
  apply tendsto_finsetSum
  intro j _
  exact (continuousAt_damped_regionTerm (t : ℂ) d (weylU a b i) (weylV a b i)
    h.d_ne_zero (h.rows i) j).tendsto
end FourierJacobi.Analysis
