-- Prove2me | solution 1 for DimdPolyLEAN.period_smul_muCircle_carrierArc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:33.128926+00:00
-- url     : https://prove2.me/submissions/bc777cf2-89d3-49e6-a5bd-78549d9c31df

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
public import Theorems.Thm_DimdPolyLEAN_carrierArc_arcSet_ae_eq_mk_image_Ioc
public import Theorems.Thm_DimdPolyLEAN_period_smul_muCircle_mk_image_carrierArc_Ioc

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {N : Nat} (k : Fin N) :
    ENNReal.ofReal (2 * Real.pi) *
        μCircle (arcSet (carrierArc N k)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  rw [MeasureTheory.measure_congr (carrierArc_arcSet_ae_eq_mk_image_Ioc k)]
  exact period_smul_μCircle_mk_image_carrierArc_Ioc k
end DimdPolyLEAN
