-- Prove2me | solution 1 for FourierJacobi.Measure.intValue_lt_one_iff_le_exp_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:27.703353+00:00
-- url     : https://prove2.me/submissions/064afc65-7179-4fc5-8665-8cec30dc3b22

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
theorem _root_.solution (z : ℤᵐ⁰) :
    z < 1 ↔ z ≤ WithZero.exp (-1 : ℤ) := by
  induction z using WithZero.expRecOn with
  | zero => simp
  | exp a =>
    change WithZero.exp a < WithZero.exp (0 : ℤ) ↔
      WithZero.exp a ≤ WithZero.exp (-1 : ℤ)
    rw [WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega
end FourierJacobi.Measure
