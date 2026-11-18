-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva39_aestrong_integrable_nonnegative_Fatou_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:54:29.423354+00:00
-- url     : https://prove2.me/submissions/7eef5bd3-9e1e-4f81-9e7c-8f878ef343d1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (Y : Ω → ℝ) (K : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hFpos : ∀ n, 0 ≤ᵐ[P] F n)
    (hYI : Integrable Y P)
    (hYpos : 0 ≤ᵐ[P] Y)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ K)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop)
    (hK : 0 ≤ K) :
    (∫ ω, Y ω ∂P) ≤ K := by
  have hFB : ∀ n, (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤
      ENNReal.ofReal K := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hFI n)
      (hFpos n)]
    exact ENNReal.ofReal_le_ofReal (hMean n)
  have hFLim :
      liminf (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P)
        atTop ≤ ENNReal.ofReal K :=
    liminf_le_of_frequently_le'
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hFB))
  have hYlin : (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) ≤
      ENNReal.ofReal K := by
    calc
      _ ≤ ∫⁻ ω, liminf (fun n =>
            ENNReal.ofReal (F n ω)) atTop ∂P :=
        lintegral_mono_ae hFatou
      _ ≤ liminf (fun n : ℕ =>
            ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) atTop :=
        lintegral_liminf_le'
          (fun n => (hFI n).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal K := hFLim
  rw [integral_eq_lintegral_of_nonneg_ae hYpos
    hYI.aestronglyMeasurable]
  have hRes := ENNReal.toReal_mono ENNReal.ofReal_ne_top hYlin
  simpa only [ENNReal.toReal_ofReal hK] using hRes
