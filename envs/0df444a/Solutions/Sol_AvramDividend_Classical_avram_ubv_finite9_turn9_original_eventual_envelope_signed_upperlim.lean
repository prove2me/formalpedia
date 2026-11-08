-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn9_original_eventual_envelope_signed_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:49:28.368425+00:00
-- url     : https://prove2.me/submissions/a9f25fc1-933d-43f6-8141-15eb8c6604c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_capped_C2_signed_integral_upperlim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite, possibly nonintegrable initial segment of a stopped Taylor
approximation does not affect its signed Levy-integral upper limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y))
    (h : ℝ → ℝ) (hhmeas : Measurable h)
    (hh_nonneg : ∀ z : ℝ, 0 ≤ h z)
    (hhfinite : (∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν) ≠ ⊤)
    (hint : Integrable h X.ν)
    (hfmeas : ∀ n : ℕ, Measurable (fun z : ℝ =>
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0)))
    (hgmeas : Measurable (fun z : ℝ =>
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0)))
    (hgabs : ∀ z : ℝ,
      |w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0)| ≤ h z)
    (hgint : Integrable (fun z : ℝ =>
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0)) X.ν)
    (hEventually : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ z : ℝ,
        |w (u n + z) - w (u n) -
          (if -1 < z then z * deriv w (u n) else 0)| ≤ h z) ∧
      Integrable (fun z : ℝ =>
        w (u n + z) - w (u n) -
          (if -1 < z then z * deriv w (u n) else 0)) X.ν) :
    let R : ℝ → ℝ → ℝ := fun a z =>
      w (a + z) - w a -
        (if -1 < z then z * deriv w a else 0)
    Filter.limsup (fun n : ℕ => ∫ z, R (u n) z ∂X.ν) atTop ≤
      ∫ z, R y z ∂X.ν := by
  intro R
  obtain ⟨N, hN⟩ := hEventually
  let v : ℕ → ℝ := fun n => if N ≤ n then u n else y
  have hev : v =ᶠ[atTop] u := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [v, hn]
  have hv : Tendsto v atTop (nhds y) := hu.congr' hev.symm
  have hvm : ∀ n, Measurable (fun z : ℝ => R (v n) z) := by
    intro n
    by_cases hn : N ≤ n
    · simpa [R, v, hn] using hfmeas n
    · simpa [R, v, hn] using hgmeas
  have hva : ∀ n z, |R (v n) z| ≤ h z := by
    intro n z
    by_cases hn : N ≤ n
    · simpa [R, v, hn] using (hN n hn).1 z
    · simpa [R, v, hn] using hgabs z
  have hvi : ∀ n, Integrable (fun z : ℝ => R (v n) z) X.ν := by
    intro n
    by_cases hn : N ≤ n
    · simpa [R, v, hn] using (hN n hn).2
    · simpa [R, v, hn] using hgint
  have hlim : Filter.limsup
      (fun n : ℕ => ∫ z, R (v n) z ∂X.ν) atTop ≤
      ∫ z, R y z ∂X.ν := by
    simpa only [R] using
      (avram_ubv_ito_jumps16_original_capped_C2_signed_integral_upperlim
        X w cap c hc hcCap hw_smooth hw0 hwcont hwneg
        y hy v hv h hhmeas hh_nonneg hhfinite hint
        hvm hgmeas hva hgabs hvi hgint)
  have heInt : (fun n : ℕ => ∫ z, R (v n) z ∂X.ν) =ᶠ[atTop]
      (fun n : ℕ => ∫ z, R (u n) z ∂X.ν) := by
    filter_upwards [hev] with n hn
    simp [hn]
  calc
    Filter.limsup (fun n : ℕ => ∫ z, R (u n) z ∂X.ν) atTop =
        Filter.limsup (fun n : ℕ => ∫ z, R (v n) z ∂X.ν) atTop :=
      (Filter.limsup_congr heInt).symm
    _ ≤ _ := hlim
