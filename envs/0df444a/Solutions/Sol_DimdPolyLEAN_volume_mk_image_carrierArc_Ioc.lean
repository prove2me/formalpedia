-- Prove2me | solution 1 for DimdPolyLEAN.volume_mk_image_carrierArc_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:09.59934+00:00
-- url     : https://prove2.me/submissions/cfbac2e7-57b4-4feb-8ae9-f22d3e953314

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
public import Theorems.Thm_DimdPolyLEAN_carrierArc_mk_preimage_image_Ioc_inter_fundamental
public import Theorems.Thm_DimdPolyLEAN_carrierArc_arcSet_ae_eq_mk_image_Ioc_volume
public import Theorems.Thm_DimdPolyLEAN_measurableSet_arcSet

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {N : Nat} (k : Fin N) :
    MeasureTheory.volume
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  have hS_null :
      MeasureTheory.NullMeasurableSet S
        (MeasureTheory.volume : MeasureTheory.Measure Circle) := by
    exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
      (carrierArc_arcSet_ae_eq_mk_image_Ioc_volume k)
  have hpre :=
    (AddCircle.measurePreserving_mk (T := 2 * Real.pi) (t := 0)).measure_preimage hS_null
  rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioc] at hpre
  change MeasureTheory.volume
      (((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi)) =
      MeasureTheory.volume S at hpre
  have hpre_set :
      ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) =
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
    simpa only [zero_add, S] using carrierArc_mk_preimage_image_Ioc_inter_fundamental k
  rw [hpre_set, Real.volume_Ioc] at hpre
  dsimp [arcLength]
  symm
  rw [← hpre]
end DimdPolyLEAN
