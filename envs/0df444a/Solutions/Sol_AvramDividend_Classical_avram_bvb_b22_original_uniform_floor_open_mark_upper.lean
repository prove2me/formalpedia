-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b22_original_uniform_floor_open_mark_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:07:40.232978+00:00
-- url     : https://prove2.me/submissions/1e5a64c1-5e1f-4a7e-a788-5b3987eb43b9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_left_sample_mark_loss_upper
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original open-mask marked-loss samples obey the closed-contact upper bound on the true uniform floor grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) (q T : ℝ) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ∀ᶠ n in atTop,
      (if 0 < U (s n) ∧ ENNReal.ofReal (U (s n)) < C then
        -(Real.exp (-(q * (s n : ℝ))) *
          ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν)
       else 0) ≤
      -(Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν) + ε := by
  intro s U hcap
  have hfloor := avram_bvb_b21_original_uniform_floor_samples_converge_from_left
    T (t : ℝ) hT (by exact_mod_cast t.2)
  have hs : Tendsto s atTop (𝓝 t) := by
    have hcomp := continuous_real_toNNReal.continuousAt.tendsto.comp hfloor.2
    simpa only [Function.comp_def, s, Real.toNNReal_coe] using hcomp
  have hs_le (n : ℕ) : s n ≤ t := by
    change Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) /
        ((n : ℝ) + 2)) ≤ t
    simpa only [Real.toNNReal_coe] using
      (Real.toNNReal_mono (hfloor.1 n))
  have hpos : ∀ᶠ n in atTop, 0 < s n :=
    hs.eventually (IsOpen.mem_nhds isOpen_Ioi htpos)
  have hleft : ∀ᶠ n in atTop, 0 < s n ∧ s n ≤ t := by
    filter_upwards [hpos] with n hn
    exact ⟨hn, hs_le n⟩
  exact avram_bvb_b21_original_left_sample_mark_loss_upper
    X x C hC D hD ω S t ht htpos hsource hFinite
    w hw_cont hw0 hw_neg hw_meas hw_smooth hw_grad
    hActivity hνatom q s hs hleft ε hε hcap
