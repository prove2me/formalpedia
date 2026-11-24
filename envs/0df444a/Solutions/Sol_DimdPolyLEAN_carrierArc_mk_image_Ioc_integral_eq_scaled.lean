-- Prove2me | solution 1 for DimdPolyLEAN.carrierArc_mk_image_Ioc_integral_eq_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:10.372283+00:00
-- url     : https://prove2.me/submissions/7c428586-8fdf-4e8b-ac69-febed75532d3

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
public import Theorems.Thm_DimdPolyLEAN_carrierArc_mk_preimage_image_Ioc_inter_fundamental
public import Theorems.Thm_DimdPolyLEAN_carrierArc_arcSet_ae_eq_mk_image_Ioc
public import Theorems.Thm_DimdPolyLEAN_measurableSet_arcSet

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    (∫ x in (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle) =
      (2 * Real.pi)⁻¹ *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let A : Set ℝ := Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let F : Set ℝ := Set.Ioc (0 : ℝ) (2 * Real.pi)
  have hS_null : MeasureTheory.NullMeasurableSet S μCircle := by
    exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
      (carrierArc_arcSet_ae_eq_mk_image_Ioc k)
  have hhaar := AddCircle.integral_haarAddCircle (T := 2 * Real.pi)
    (f := S.indicator f)
  change ∫ x, S.indicator f x ∂ μCircle =
    (2 * Real.pi)⁻¹ • ∫ x, S.indicator f x at hhaar
  rw [MeasureTheory.integral_indicator₀ hS_null] at hhaar
  have hpre := AddCircle.integral_preimage (T := 2 * Real.pi) (t := 0)
    (f := S.indicator f)
  have hpre' :
      (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) =
        ∫ x : Circle, S.indicator f x := by simpa only [zero_add, F] using hpre
  have hfund_to_A :
      (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) =
        ∫ t in A, f (QuotientAddGroup.mk t : Circle) := by
    have hpre_set :
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩ F = A := by
      exact carrierArc_mk_preimage_image_Ioc_inter_fundamental k
    have hfun : Set.EqOn
        (fun t : ℝ => S.indicator f (QuotientAddGroup.mk t : Circle))
        (fun t : ℝ => A.indicator
          (fun y : ℝ => f (QuotientAddGroup.mk y : Circle)) t)
        F := by
      intro t htF
      by_cases htS : (QuotientAddGroup.mk t : Circle) ∈ S
      · have htA : t ∈ A := by
          have htpre :
              t ∈ ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩ F :=
            ⟨htS, htF⟩
          simpa only [hpre_set] using htpre
        simp [Set.indicator_of_mem htS, Set.indicator_of_mem htA]
      · have htA : t ∉ A := by
          intro htA
          exact htS ⟨t, htA, rfl⟩
        simp [Set.indicator_of_notMem htS, Set.indicator_of_notMem htA]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hfun]
    rw [MeasureTheory.setIntegral_indicator (μ := MeasureTheory.volume) (s := F) (t := A)
      measurableSet_Ioc]
    have h_inter : F ∩ A = A := by
      ext t
      constructor
      · intro ht
        exact ht.2
      · intro htA
        exact ⟨⟨lt_of_le_of_lt (carrierArc_left_nonneg k) htA.1,
          le_trans htA.2 (carrierArc_right_le_period k)⟩, htA⟩
    rw [h_inter]
  calc
    (∫ x in (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle)
        = ∫ x in S, f x ∂ μCircle := by rfl
    _ = (2 * Real.pi)⁻¹ * ∫ x : Circle, S.indicator f x := by simpa only [mul_inv_rev,
                                                                smul_eq_mul] using
      hhaar
    _ = (2 * Real.pi)⁻¹ *
        (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) := by rw [hpre']
    _ = (2 * Real.pi)⁻¹ * ∫ t in A, f (QuotientAddGroup.mk t : Circle) := by rw [hfund_to_A]
    _ = (2 * Real.pi)⁻¹ *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) := by rfl
end DimdPolyLEAN
