-- Prove2me | solution 2 for FiniteEnergyPlane.setIntegral_annulus_eq_integral_circleMap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T23:08:45.765286+00:00
-- url     : https://prove2.me/submissions/ccd4728a-3535-4f87-a98c-39237033eae9

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Integral over an annulus in polar coordinates. -/
theorem setIntegral_annulus_eq_integral_circleMap_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (closedBall 0 b \ ball 0 a)) :
    ∫ z in ball 0 b \ ball 0 a, f z = ∫ r in a..b, r • ∫ θ in 0..2 * π, f (circleMap 0 r θ) := by
  set A := ball (0 : ℂ) b \ ball 0 a with hAdef
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hpol : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, zero_add,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hmemA : ∀ r θ : ℝ, 0 < r → (circleMap 0 r θ ∈ A ↔ r ∈ Ico a b) := by
    intro r θ hr
    simp only [hAdef, mem_diff, mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hr,
      mem_Ico, not_lt]
    tauto
  set S : Set (ℝ × ℝ) := Ico a b ×ˢ Ioo (-π) π with hS
  set H : ℝ × ℝ → F := S.indicator (fun p => p.1 • f (circleMap 0 p.1 p.2)) with hH
  have hcm : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    unfold circleMap; fun_prop
  have hHi : Integrable H := by
    rw [hH, integrable_indicator_iff (measurableSet_Ico.prod measurableSet_Ioo)]
    have hK : IsCompact (Icc a b ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
    have hc : ContinuousOn (fun p : ℝ × ℝ => p.1 • f (circleMap 0 p.1 p.2))
        (Icc a b ×ˢ Icc (-π) π) := by
      refine continuousOn_fst.smul (hf.comp hcm.continuousOn ?_)
      rintro ⟨r, θ⟩ ⟨hr, -⟩
      have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
      refine ⟨?_, ?_⟩
      · simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hr0]
        exact hr.2
      · simp only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hr0, not_lt]
        exact hr.1
    exact (hc.integrableOn_compact hK).mono_set
      (prod_mono Ico_subset_Icc_self Ioo_subset_Icc_self)
  have h1 : ∫ z in A, f z = ∫ p in polarCoord.target, p.1 • A.indicator f
      (Complex.polarCoord.symm p) := by
    rw [← integral_indicator hA, Complex.integral_comp_polarCoord_symm]
  have h2 : ∫ p in polarCoord.target, p.1 • A.indicator f (Complex.polarCoord.symm p) =
      ∫ p in polarCoord.target, H p := by
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    obtain ⟨r, θ⟩ := p
    have hr : 0 < r := hp.1
    have hθ : θ ∈ Ioo (-π) π := hp.2
    rw [hpol]
    simp only [hH, hS, indicator, mem_prod, hmemA r θ hr]
    by_cases h : r ∈ Ico a b
    · simp [h, hθ]
    · simp [h]
  have h3 : ∫ p in polarCoord.target, H p =
      ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, H (r, θ) := by
    rw [polarCoord_target, Measure.volume_eq_prod]
    exact setIntegral_prod H hHi.integrableOn
  have h4 : ∀ r : ℝ, ∫ θ in Ioo (-π) π, H (r, θ) =
      (Ico a b).indicator (fun r => r • ∫ θ in Ioo (-π) π, f (circleMap 0 r θ)) r := by
    intro r
    by_cases h : r ∈ Ico a b
    · rw [indicator_of_mem h, ← integral_smul]
      refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
      simp [hH, hS, indicator, h, hθ]
    · rw [indicator_of_notMem h]
      refine (setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)).trans (integral_zero _ _)
      simp [hH, hS, indicator, h]
  have h5 : ∀ r : ℝ, ∫ θ in Ioo (-π) π, f (circleMap 0 r θ) =
      ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 r θ) := by
    intro r
    have hper : ∫ θ in (-π)..π, f (circleMap 0 r θ) =
        ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 r θ) := by
      have h := ((periodic_circleMap 0 r).comp f).intervalIntegral_add_eq (-π) 0
      rw [show -π + 2 * π = π by ring, zero_add] at h
      exact h
    rw [← hper, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
  rw [h1, h2, h3]
  simp_rw [h4, h5]
  rw [setIntegral_indicator measurableSet_Ico,
    show Ioi (0 : ℝ) ∩ Ico a b = Ico a b from inter_eq_right.2 (fun r hr => lt_of_lt_of_le ha hr.1),
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (closedBall 0 b \ ball 0 a)) :
    ∫ z in ball 0 b \ ball 0 a, f z = ∫ r in a..b, r • ∫ θ in 0..2 * π, f (circleMap 0 r θ) :=
  setIntegral_annulus_eq_integral_circleMap_aux ha hab hf
