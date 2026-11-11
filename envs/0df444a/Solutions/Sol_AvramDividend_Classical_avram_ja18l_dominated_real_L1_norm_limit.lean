-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18l_dominated_real_L1_norm_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:33:41.22568+00:00
-- url     : https://prove2.me/submissions/16a1f3ff-d6af-4877-a711-569ae8be939d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Lebesgue dominated convergence for the real L1 distance on
the original measure, expressed using the Mathlib extended seminorm. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g B : Ω → ℝ)
    (hf : ∀ n : ℕ, AEStronglyMeasurable (f n) P)
    (hBi : Integrable B P)
    (hBound : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n : ℕ => eLpNorm (f n - g) 1 P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hGmeas : AEStronglyMeasurable g P :=
    aestronglyMeasurable_of_tendsto_ae atTop hf hLimit
  have hAllBound : ∀ᵐ ω ∂P, ∀ n : ℕ, ‖f n ω‖ ≤ B ω := by
    exact ae_all_iff.mpr hBound
  have hGbound : ∀ᵐ ω ∂P, ‖g ω‖ ≤ B ω := by
    filter_upwards [hLimit, hAllBound] with ω hωlim hωB
    exact le_of_tendsto hωlim.norm
      (Filter.Eventually.of_forall (fun n => hωB n))
  have hMeas (n : ℕ) :
      AEMeasurable (fun ω => ‖f n ω - g ω‖ₑ) P :=
    ((hf n).sub hGmeas).enorm
  have hDom (n : ℕ) :
      ∀ᵐ ω ∂P, ‖f n ω - g ω‖ₑ ≤ 2 * ‖B ω‖ₑ := by
    filter_upwards [hBound n, hGbound] with ω hn hg
    have hb : 0 ≤ B ω := le_trans (norm_nonneg _) hn
    have hfn : ‖f n ω‖ₑ ≤ ENNReal.ofReal (B ω) := by
      simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hn
    have hgn : ‖g ω‖ₑ ≤ ENNReal.ofReal (B ω) := by
      simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hg
    calc
      ‖f n ω - g ω‖ₑ ≤ ‖f n ω‖ₑ + ‖g ω‖ₑ := enorm_sub_le
      _ ≤ ENNReal.ofReal (B ω) + ENNReal.ofReal (B ω) :=
        add_le_add hfn hgn
      _ = 2 * ‖B ω‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hb]
        ring
  have hFinite : (∫⁻ ω, 2 * ‖B ω‖ₑ ∂P) ≠ ⊤ := by
    rw [lintegral_const_mul' 2 (fun ω => ‖B ω‖ₑ) (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num) (ne_of_lt hBi.hasFiniteIntegral)
  have hLimitEnorm : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ‖f n ω - g ω‖ₑ)
        atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [hLimit] with ω hω
    convert (hω.sub tendsto_const_nhds).enorm using 1 <;> simp
  have hIntLimit :=
    tendsto_lintegral_of_dominated_convergence'
      (fun ω => 2 * ‖B ω‖ₑ) hMeas hDom hFinite hLimitEnorm
  simpa only [eLpNorm_one_eq_lintegral_enorm, lintegral_zero, Pi.sub_apply] using hIntLimit
