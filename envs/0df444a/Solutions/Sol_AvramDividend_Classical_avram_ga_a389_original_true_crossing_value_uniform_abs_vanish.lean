-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a389_original_true_crossing_value_uniform_abs_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:14:01.993068+00:00
-- url     : https://prove2.me/submissions/3990dc97-5cb2-446e-b702-6ffe40b474a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a401_original_inclusive_crossing_spatial_absolute_sum_ae_zero
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
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : Ω → ℝ≥0 → ℝ := fun ω t => x + X.X t ω - rightLimit D t ω
    let Val : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      E (ρ ω) * (w (Y ω (s m i) +
        (X.X (ρ ω) ω - X.X (s m i) ω)) - w (Y ω (s m i)))
    ∃ B : ℕ → Ω → ℝ,
      (∀ (m : ℕ) (ω : Ω), 0 ≤ B m ω) ∧
      (∀ (m : ℕ) (ω : Ω) (i : ℕ), i < m →
        s m i < ρ ω → ρ ω ≤ s m (i + 1) →
        |Val m i ω| ≤ B m ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun m => B m ω) atTop (nhds (0 : ℝ))) := by
  classical
  intro Δ s E Y Val
  let CrossMask : ℕ → ℕ → Ω → Prop := fun m i ω =>
    s m i < ρ ω ∧ ρ ω ≤ s m i + Δ m
  let Err : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if CrossMask m i ω then
        |E (ρ ω) *
          (w (x + X.X (ρ ω) ω - rightLimit D (s m i) ω) -
            w (x + X.X (s m i) ω - rightLimit D (s m i) ω))|
      else 0
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by
    exact avram_ga_a401_original_inclusive_crossing_spatial_absolute_sum_ae_zero
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  refine ⟨Err, ?_, ?_, hlim⟩
  · intro m ω
    dsimp [Err]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  · intro m ω i hi hs he
    have hstep : s m (i+1) = s m i + Δ m := by
      dsimp [s]
      rw [Nat.cast_succ, add_mul, one_mul]
    have hc : CrossMask m i ω := ⟨hs, by simpa only [hstep] using he⟩
    have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
    have hsingle :
        |E (ρ ω) *
          (w (x + X.X (ρ ω) ω - rightLimit D (s m i) ω) -
            w (x + X.X (s m i) ω - rightLimit D (s m i) ω))| ≤
        Err m ω := by
      dsimp [Err]
      have hb := Finset.single_le_sum
        (s := Finset.range m)
        (f := fun k => if CrossMask m k ω then
          |E (ρ ω) *
            (w (x + X.X (ρ ω) ω - rightLimit D (s m k) ω) -
              w (x + X.X (s m k) ω - rightLimit D (s m k) ω))|
          else 0)
        (fun k hk => by split_ifs <;> positivity) hmem
      simpa [hc] using hb
    have heq : Val m i ω =
      E (ρ ω) *
        (w (x + X.X (ρ ω) ω - rightLimit D (s m i) ω) -
          w (x + X.X (s m i) ω - rightLimit D (s m i) ω)) := by
      dsimp [Val,Y]
      ring
    simpa only [heq] using hsingle
