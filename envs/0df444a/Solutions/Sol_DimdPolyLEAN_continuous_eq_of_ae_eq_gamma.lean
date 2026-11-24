-- Prove2me | solution 1 for DimdPolyLEAN.continuous_eq_of_ae_eq_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:50.261056+00:00
-- url     : https://prove2.me/submissions/d3d595ea-3b91-44f0-ad66-bbf690337e6c

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
section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
private theorem gamma_d_isOpenPosMeasure (d : Nat) :
    MeasureTheory.Measure.IsOpenPosMeasure (gammaD d) := by
  refine ⟨?_⟩
  intro U hU hUne
  rcases hUne with ⟨x, hxU⟩
  rcases Metric.isOpen_iff.mp hU x hxU with ⟨r, hr, hball⟩
  let w : Cd d → ENNReal := fun z => ENNReal.ofReal (gaussianDensity d z)
  have hgauss_cont : Continuous (gaussianDensity d) := by
    unfold gaussianDensity
    fun_prop
  have hw_meas : Measurable w := by exact ENNReal.measurable_ofReal.comp hgauss_cont.measurable
  have hw_ne_zero : ∀ z : Cd d, w z ≠ 0 := by
    intro z
    have hpos : 0 < gaussianDensity d z := by
      unfold gaussianDensity
      positivity
    simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le, gt_iff_lt, w] using hpos
  have hball_ne : gammaD d (Metric.ball x r) ≠ 0 := by
    intro hzero
    have hzero' : MeasureTheory.volume.withDensity w (Metric.ball x r) = 0 := by
      simpa only [gammaD, w] using hzero
    have hvol_zero :
        MeasureTheory.volume ({z : Cd d | w z ≠ 0} ∩ Metric.ball x r) = 0 :=
      (MeasureTheory.withDensity_apply_eq_zero hw_meas).1 hzero'
    have hball_eq :
        {z : Cd d | w z ≠ 0} ∩ Metric.ball x r = Metric.ball x r := by
      ext z
      simp [hw_ne_zero z]
    have hball_vol_zero : MeasureTheory.volume (Metric.ball x r) = 0 := by
      simpa only [ne_eq, hball_eq] using hvol_zero
    exact (Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Cd d)) x hr).ne'
      hball_vol_zero
  exact fun hzero => hball_ne (MeasureTheory.measure_mono_null hball hzero)
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) {f g : Cd d -> ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfg : f =ᵐ[gammaD d] g) :
    f = g := by
  let _ := hd
  /-
  Scaffolding contract:
  this packages the a.e.-to-everywhere uniqueness bridge for continuous
  representatives under the frozen Gaussian measure.
  -/
  have := gamma_d_isOpenPosMeasure d
  exact MeasureTheory.Measure.eq_of_ae_eq hfg hf hg
end DimdPolyLEAN
