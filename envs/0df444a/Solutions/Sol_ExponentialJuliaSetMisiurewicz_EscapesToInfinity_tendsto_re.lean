-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.EscapesToInfinity.tendsto_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:46.974039+00:00
-- url     : https://prove2.me/submissions/fd4e28f6-3838-4600-b102-f2c375965690

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_ExpChaotic_Dynamics
import Definitions.Def_ExpChaotic_PaperConsequences
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
namespace EscapesToInfinity
theorem _root_.solution {z : ℂ} (hz : EscapesToInfinity z) :
    Tendsto (fun n => (expIterate n z).re) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨N, hN⟩ := hz (Real.exp R)
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have h := hN (n + 1) (by omega)
  simpa only [expIterate_succ, Complex.norm_exp, Real.exp_le_exp] using h
end EscapesToInfinity
end ExponentialJuliaSetMisiurewicz
