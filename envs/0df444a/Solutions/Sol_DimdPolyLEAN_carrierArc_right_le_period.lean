-- Prove2me | solution 1 for DimdPolyLEAN.carrierArc_right_le_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:05:00.781798+00:00
-- url     : https://prove2.me/submissions/8b5633d8-9043-4de4-b0e9-4819a06146bc

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {N : Nat} (k : Fin N) :
    (carrierArc N k).right <= 2 * Real.pi := by
  unfold carrierArc
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast k.pos
  have hle : ((k.1 + 1 : Nat) : ℝ) <= (N : ℝ) := by exact_mod_cast k.2
  have hT_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  calc
    (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ)
        <= (2 * Real.pi) * (N : ℝ) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hT_nonneg)
        (le_of_lt hNpos)
    _ = 2 * Real.pi := by field_simp [ne_of_gt hNpos]
end DimdPolyLEAN
