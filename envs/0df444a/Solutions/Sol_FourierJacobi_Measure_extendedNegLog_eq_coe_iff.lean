-- Prove2me | solution 1 for FourierJacobi.Measure.extendedNegLog_eq_coe_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:25.389729+00:00
-- url     : https://prove2.me/submissions/e38d914f-f907-4276-a35e-ffa02ba12fee

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
namespace FourierJacobi.Measure
theorem _root_.solution (z : ℤᵐ⁰) (n : ℤ) :
    extendedNegLog z = (n : WithTop ℤ) ↔ z = WithZero.exp (-n) := by
  induction z using WithZero.expRecOn with
  | zero =>
    constructor
    · intro h
      exact False.elim (WithTop.top_ne_coe h)
    · intro h
      exact False.elim (WithZero.exp_ne_zero h.symm)
  | exp a =>
    simp only [extendedNegLog_exp, WithTop.coe_inj, WithZero.exp_inj]
    omega
end FourierJacobi.Measure
