-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:24:38.877208+00:00
-- url     : https://prove2.me/submissions/97d3ce27-d096-4ecb-a920-258dd005d2cc

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Signed supermartingale mesh bounds pass to the nonnegative stopped value by Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : ℝ) (Y : Ω → ℝ)
    (F R : ℕ → Ω → ℝ)
    (hYInt : Integrable Y P)
    (hYNonneg : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0)
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ K + R n ω)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ K := by
  have hFMean (n : ℕ) : (∫ ω, F n ω ∂P) ≤ K := by
    have hRInt := (hR n).1
    have hRMean := (hR n).2
    calc
      _ ≤ (∫ ω, K + R n ω ∂P) :=
        integral_mono_ae (hFInt n) ((integrable_const K).add hRInt)
          (hBound n)
      _ = K + (∫ ω, R n ω ∂P) := by
        rw [integral_add (integrable_const K) hRInt]
        simp
      _ ≤ K := by linarith only [hRMean]
  have hKNonneg : 0 ≤ K :=
    (integral_nonneg_of_ae (hFNonneg 0)).trans (hFMean 0)
  have hFMeas' (n : ℕ) :
      Measurable (fun ω => ENNReal.ofReal (F n ω)) :=
    (hFMeas n).ennreal_ofReal
  have hFatouIntegral :
      (∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂P) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) atTop :=
    lintegral_liminf_le hFMeas'
  have hFBoundEnn (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤ ENNReal.ofReal K := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFInt n) (hFNonneg n)]
    exact ENNReal.ofReal_le_ofReal (hFMean n)
  have hBdd :
      Filter.IsBoundedUnder (fun a b : ℝ≥0∞ => a ≥ b)
        (atTop : Filter ℕ)
        (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) := by
    refine ⟨0, ?_⟩
    exact Filter.Eventually.of_forall (fun n => bot_le)
  have hLiminf :
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) atTop ≤
      ENNReal.ofReal K := by
    apply Filter.liminf_le_of_le hBdd
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hFBoundEnn n)
  have hLower :
      (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) ≤
      (∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂P) :=
    lintegral_mono_ae hFatou
  have hExpected :
      ENNReal.ofReal (∫ ω, Y ω ∂P) ≤ ENNReal.ofReal K := by
    rw [ofReal_integral_eq_lintegral_ofReal hYInt hYNonneg]
    exact (hLower.trans hFatouIntegral).trans hLiminf
  exact (ENNReal.ofReal_le_ofReal_iff hKNonneg).mp hExpected
