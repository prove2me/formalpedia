-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a565_two_stage_Fatou_expected_budget_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:52:34.139203+00:00
-- url     : https://prove2.me/submissions/a07df46f-f581-40de-b14e-25272e29ce3a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (K : ℝ) (hK : 0 ≤ K)
    (Y : Ω → ℝ) (F : ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ≥0∞)
    (hYm : AEStronglyMeasurable Y P)
    (hYnn : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hFI : ∀ n, Integrable (F n) P)
    (hGm : ∀ n, Measurable (G n))
    (hFnear : ∀ n, ∀ᵐ ω ∂P,
      ENNReal.ofReal (F n ω) ≤ liminf (fun m => G m ω) atTop)
    (hGB : ∀ m, (∫⁻ ω, G m ω ∂P) ≤ ENNReal.ofReal K)
    (hYnear : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ K := by
  classical
  have hGBlim :
      liminf (fun m : ℕ => ∫⁻ ω, G m ω ∂P) atTop ≤ ENNReal.ofReal K :=
    liminf_le_of_frequently_le'
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hGB))
  have hFB : ∀ n, (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤ ENNReal.ofReal K := by
    intro n
    calc
      (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤
          ∫⁻ ω, liminf (fun m => G m ω) atTop ∂P :=
        lintegral_mono_ae (hFnear n)
      _ ≤ liminf (fun m : ℕ => ∫⁻ ω, G m ω ∂P) atTop :=
        lintegral_liminf_le hGm
      _ ≤ ENNReal.ofReal K := hGBlim
  have hFLim :
      liminf (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) atTop ≤
        ENNReal.ofReal K :=
    liminf_le_of_frequently_le'
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hFB))
  have hYlin :
      (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) ≤ ENNReal.ofReal K := by
    calc
      (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) ≤
          ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂P :=
        lintegral_mono_ae hYnear
      _ ≤ liminf (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) atTop :=
        lintegral_liminf_le' (fun n => (hFI n).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal K := hFLim
  rw [integral_eq_lintegral_of_nonneg_ae hYnn hYm]
  exact (ENNReal.toReal_mono (by simp) hYlin).trans_eq
    (by simp [hK])
