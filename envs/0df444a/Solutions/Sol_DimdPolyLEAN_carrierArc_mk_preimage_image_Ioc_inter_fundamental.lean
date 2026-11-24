-- Prove2me | solution 1 for DimdPolyLEAN.carrierArc_mk_preimage_image_Ioc_inter_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:38.915123+00:00
-- url     : https://prove2.me/submissions/453de5d8-0a6b-45d4-b4c1-7146a59630a4

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
public import Theorems.Thm_DimdPolyLEAN_carrierArc_left_nonneg
public import Theorems.Thm_DimdPolyLEAN_carrierArc_right_le_period
public import Theorems.Thm_DimdPolyLEAN_quotient_mk_injOn_Ioc_zero_period

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {N : Nat} (k : Fin N) :
    ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹'
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∩
      Set.Ioc (0 : ℝ) (2 * Real.pi)) =
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  ext x
  constructor
  · intro hx
    rcases hx.1 with ⟨y, hy, hyx⟩
    have hy_fund : y ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg k) hy.1,
        le_trans hy.2 (carrierArc_right_le_period k)⟩
    have hxy : y = x :=
      quotient_mk_injOn_Ioc_zero_period hy_fund hx.2 hyx
    rwa [← hxy]
  · intro hx
    constructor
    · exact ⟨x, hx, rfl⟩
    · exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg k) hx.1,
        le_trans hx.2 (carrierArc_right_le_period k)⟩
end DimdPolyLEAN
