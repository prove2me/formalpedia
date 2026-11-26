-- Prove2me | solution 1 for EasyEstimateForMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:44.690538+00:00
-- url     : https://prove2.me/submissions/f6475b56-fd25-45af-b214-835e28f34b49

import Definitions.Def_Tablet_massOfFunctional
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_EasyEstimateForMass
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) :
    IsAdmissible (curveCurrent γ) (curveMeasure γ) ∧
      massOfFunctional (curveCurrent γ) ≤ ENNReal.ofReal γ.len := by
-- BODY
  have hmeasble : Measurable γ.toFun := (CurveLipschitz γ).continuous.measurable
  have huniv : curveMeasure γ Set.univ = ENNReal.ofReal γ.len := by
    show Measure.map γ.toFun (volume.restrict (Set.Icc 0 γ.len)) Set.univ = ENNReal.ofReal γ.len
    rw [Measure.map_apply hmeasble MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hfin : IsFiniteMeasure (curveMeasure γ) := ⟨by rw [huniv]; exact ENNReal.ofReal_lt_top⟩
  have hadm : IsAdmissible (curveCurrent γ) (curveMeasure γ) := by
    refine ⟨hfin, ?_⟩
    intro ω
    have hlip : LipschitzWith ω.piLip (ω.pi ∘ γ.toFun) := by
      have h := ω.pi_lipschitz.comp (CurveLipschitz γ)
      simpa using h
    have hbound : ∀ t : ℝ,
        |ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t| ≤ (ω.piLip : ℝ) * |ω.f (γ.toFun t)| := by
      intro t
      rw [abs_mul, mul_comm (|ω.f (γ.toFun t)|)]
      by_cases hd : DifferentiableAt ℝ (ω.pi ∘ γ.toFun) t
      · have hderiv_le : |deriv (ω.pi ∘ γ.toFun) t| ≤ (ω.piLip : ℝ) := by
          have h := hd.hasDerivAt.le_of_lipschitz hlip
          simpa using h
        exact mul_le_mul_of_nonneg_right hderiv_le (abs_nonneg _)
      · rw [deriv_zero_of_not_differentiableAt hd]
        simpa using mul_nonneg ω.piLip.coe_nonneg (abs_nonneg (ω.f (γ.toFun t)))
    have hfcont : Continuous (fun t : ℝ => |ω.f (γ.toFun t)|) :=
      (ω.f_lipschitz.continuous.comp (CurveLipschitz γ).continuous).abs
    have hbdint : IntervalIntegrable (fun t : ℝ => (ω.piLip : ℝ) * |ω.f (γ.toFun t)|)
        volume 0 γ.len :=
      (continuous_const.mul hfcont).intervalIntegrable 0 γ.len
    have hcurrbound : |curveCurrent γ ω|
        ≤ ∫ t in (0:ℝ)..γ.len, (ω.piLip : ℝ) * |ω.f (γ.toFun t)| := by
      have hnorm : ‖∫ t in (0:ℝ)..γ.len, ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t‖
          ≤ ∫ t in (0:ℝ)..γ.len, (ω.piLip : ℝ) * |ω.f (γ.toFun t)| :=
        intervalIntegral.norm_integral_le_of_norm_le γ.len_nonneg
          (Filter.Eventually.of_forall
            (fun t (_ : t ∈ Set.Ioc (0:ℝ) γ.len) => by simpa [Real.norm_eq_abs] using hbound t))
          hbdint
      simpa [curveCurrent, Real.norm_eq_abs] using hnorm
    have hpull : (∫ t in (0:ℝ)..γ.len, (ω.piLip : ℝ) * |ω.f (γ.toFun t)|)
        = (ω.piLip : ℝ) * ∫ t in (0:ℝ)..γ.len, |ω.f (γ.toFun t)| :=
      intervalIntegral.integral_const_mul _ _
    have hfmeas : Measurable (fun x : E => ENNReal.ofReal |ω.f x|) :=
      ENNReal.measurable_ofReal.comp ω.f_lipschitz.continuous.abs.measurable
    have hlint : (∫⁻ x, ENNReal.ofReal |ω.f x| ∂(curveMeasure γ))
        = ∫⁻ t, ENNReal.ofReal |ω.f (γ.toFun t)| ∂(volume.restrict (Set.Icc 0 γ.len)) := by
      show (∫⁻ x, ENNReal.ofReal |ω.f x|
          ∂(Measure.map γ.toFun (volume.restrict (Set.Icc 0 γ.len))))
        = ∫⁻ t, ENNReal.ofReal |ω.f (γ.toFun t)| ∂(volume.restrict (Set.Icc 0 γ.len))
      exact lintegral_map hfmeas hmeasble
    have hintIcc : IntegrableOn (fun t : ℝ => |ω.f (γ.toFun t)|) (Set.Icc 0 γ.len) volume :=
      hfcont.integrableOn_Icc
    have hlint2 : (∫⁻ t, ENNReal.ofReal |ω.f (γ.toFun t)| ∂(volume.restrict (Set.Icc 0 γ.len)))
        = ENNReal.ofReal (∫ t in Set.Icc 0 γ.len, |ω.f (γ.toFun t)| ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hintIcc
        (Filter.Eventually.of_forall (fun t => abs_nonneg _))).symm
    have hIccIoc : (∫ t in Set.Icc 0 γ.len, |ω.f (γ.toFun t)| ∂volume)
        = ∫ t in Set.Ioc 0 γ.len, |ω.f (γ.toFun t)| ∂volume :=
      integral_Icc_eq_integral_Ioc
    have hIoc : (∫ t in Set.Ioc 0 γ.len, |ω.f (γ.toFun t)| ∂volume)
        = ∫ t in (0:ℝ)..γ.len, |ω.f (γ.toFun t)| :=
      (intervalIntegral.integral_of_le γ.len_nonneg).symm
    have hRHS : (∫⁻ x, ENNReal.ofReal |ω.f x| ∂(curveMeasure γ))
        = ENNReal.ofReal (∫ t in (0:ℝ)..γ.len, |ω.f (γ.toFun t)|) := by
      rw [hlint, hlint2, hIccIoc, hIoc]
    calc ENNReal.ofReal |curveCurrent γ ω|
        ≤ ENNReal.ofReal (∫ t in (0:ℝ)..γ.len, (ω.piLip : ℝ) * |ω.f (γ.toFun t)|) :=
          ENNReal.ofReal_le_ofReal hcurrbound
      _ = ENNReal.ofReal ((ω.piLip : ℝ) * ∫ t in (0:ℝ)..γ.len, |ω.f (γ.toFun t)|) := by
          rw [hpull]
      _ = (ω.piLip : ℝ≥0∞) * ENNReal.ofReal (∫ t in (0:ℝ)..γ.len, |ω.f (γ.toFun t)|) := by
          rw [ENNReal.ofReal_mul ω.piLip.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      _ = (ω.piLip : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal |ω.f x| ∂(curveMeasure γ) := by
          rw [hRHS]
  refine ⟨hadm, ?_⟩
  have hle : massOfFunctional (curveCurrent γ) ≤ (curveMeasure γ) Set.univ :=
    iInf_le (fun μ : {μ : Measure E // IsAdmissible (curveCurrent γ) μ} => μ.1 Set.univ)
      ⟨curveMeasure γ, hadm⟩
  rwa [huniv] at hle
