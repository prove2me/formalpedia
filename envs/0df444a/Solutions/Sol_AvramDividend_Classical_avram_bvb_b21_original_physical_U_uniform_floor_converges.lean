-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_physical_U_uniform_floor_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:27:26.295041+00:00
-- url     : https://prove2.me/submissions/81a91cd6-6862-4bf7-bdda-7de60fccec66

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The true original reserve is stable along uniform left-grid samples. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (T : ℝ) (hT : 0 < T) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    Tendsto (fun n => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (s n))
      atTop (𝓝 (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t)) := by
  let v : ℕ → ℝ := fun n => T *
    (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2)
  let s : ℕ → ℝ≥0 := fun n => Real.toNNReal (v n)
  have hfloor := avram_bvb_b21_original_uniform_floor_samples_converge_from_left
    T (t : ℝ) hT t.property
  have hn (n : ℕ) : 0 ≤ v n := by
    dsimp [v]
    positivity
  have hs_le (n : ℕ) : s n ≤ t := by
    apply NNReal.coe_le_coe.mp
    simpa only [s, v, Real.coe_toNNReal _ (hn n)] using hfloor.1 n
  have hs_tend : Tendsto s atTop (𝓝 t) := by
    have hc := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hfloor.2
    rw [Real.toNNReal_coe] at hc
    change Tendsto (Real.toNNReal ∘ v) atTop (𝓝 t)
    exact hc
  have hs_pos : ∀ᶠ n in atTop, 0 < s n :=
    hs_tend.eventually (Ioi_mem_nhds htpos)
  have hs_mem : ∀ᶠ n in atTop, s n ∈ Ioc 0 t := by
    filter_upwards [hs_pos] with n hn'
    exact ⟨hn', hs_le n⟩
  have hs_within : Tendsto s atTop (𝓝[Ioc 0 t] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs_tend, hs_mem⟩
  exact (avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
    X x C D hD ω S t ht htpos hsource).tendsto.comp hs_within
