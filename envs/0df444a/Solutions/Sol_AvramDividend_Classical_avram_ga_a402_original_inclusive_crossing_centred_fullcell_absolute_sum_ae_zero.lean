-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a402_original_inclusive_crossing_centred_fullcell_absolute_sum_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:36:53.361199+00:00
-- url     : https://prove2.me/submissions/5d0b41ba-cf5a-4711-82c2-a27aceb5b959

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
import Theorems.Thm_AvramDividend_Classical_avram_ga_a53_original_uniform_mesh_drift_eventually_small
import Theorems.Thm_AvramDividend_Classical_avram_ga_a411_unique_masked_uniform_vanishing_abs_diff
import Theorems.Thm_AvramDividend_Classical_avram_ga_a416_monotone_grid_unique_inclusive_crossing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let CrossMask : ℕ → ℕ → Ω → Prop := fun m i ω =>
      s m i < ρ ω ∧ ρ ω ≤ s m i + Δ m
    let Err : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if CrossMask m i ω then
          |X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c|
        else 0
    ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by
  classical
  intro Δ s CrossMask Err
  have hStep (m i : ℕ) : s m (i+1) = s m i + Δ m := by
    dsimp [s]
    rw [Nat.cast_succ, add_mul, one_mul]
  have hUnique (ω : Ω) (m i j : ℕ)
      (hi : CrossMask m i ω) (hj : CrossMask m j ω) : i = j := by
    have hd : 0 < Δ m := by
      have hn' : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
      exact div_pos hn' (by positivity)
    have hs : StrictMono (s m) := by
      intro a b hab
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hab) hd
    exact avram_ga_a416_monotone_grid_unique_inclusive_crossing
      (s m) hs (ρ ω) i j
      ⟨hi.1, by rw [hStep m i]; exact hi.2⟩
      ⟨hj.1, by rw [hStep m j]; exact hj.2⟩
  have hDrift (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ m : ℕ in atTop, |(Δ m : ℝ) * X.c| ≤ ε / 2 := by
    simpa only [Δ] using
      avram_ga_a53_original_uniform_mesh_drift_eventually_small
        n X.c ε hε
  filter_upwards
    [avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
      X hNuZero n] with ω hRaw
  have hRawCell (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ m : ℕ in atTop, ∀ i < m,
        |X.X (s m i + Δ m) ω - X.X (s m i) ω| < ε / 2 := by
    have he : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨k,hk⟩ := hRaw (ε / 2) he
    apply Filter.eventually_atTop.2
    refine ⟨k, ?_⟩
    intro m hm i hi
    simpa only [s, Δ] using hk m hm i hi
  have hSum :=
    avram_ga_a411_unique_masked_uniform_vanishing_abs_diff
      (fun m i => CrossMask m i ω)
      (fun m i => X.X (s m i + Δ m) ω - X.X (s m i) ω)
      (fun m => (Δ m : ℝ) * X.c)
      (hUnique ω) hRawCell hDrift
  simpa only [Err] using hSum
