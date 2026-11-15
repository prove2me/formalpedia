-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a405_original_inclusive_crossing_HJB_fullcell_absolute_sum_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:37:14.628335+00:00
-- url     : https://prove2.me/submissions/033b6f4c-699d-41bb-91db-3dd3fab6e438

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a402_original_inclusive_crossing_centred_fullcell_absolute_sum_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a416_monotone_grid_unique_inclusive_crossing
import Theorems.Thm_AvramDividend_Classical_avram_ga_a417_unique_masked_quadratic_limit_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ga_a418_original_Gaussian_crossing_scalar_fullcell_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
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
          let z := X.X (s m i + Δ m) ω - X.X (s m i) ω -
            (Δ m : ℝ) * X.c
          |Real.exp (-(q * (s m i : ℝ))) *
            (deriv w (x + X.X (s m i) ω - rightLimit D (s m i) ω) * z +
              (iteratedDeriv 2 w
                (x + X.X (s m i) ω - rightLimit D (s m i) ω) / 2) *
                (z^2 - (Δ m : ℝ) * X.σ^2)) +
            (Δ m : ℝ) * Real.exp (-(q * (s m i : ℝ))) *
              X.generator w (x + X.X (s m i) ω - rightLimit D (s m i) ω)|
        else 0
    ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by
  classical
  intro Δ s CrossMask Err
  obtain ⟨K,hK,hCell⟩ :=
    avram_ga_a418_original_Gaussian_crossing_scalar_fullcell_quadratic_bound
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  have hSource :=
    avram_ga_a402_original_inclusive_crossing_centred_fullcell_absolute_sum_ae_zero
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  have hWidth : Tendsto (fun m : ℕ => (Δ m : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    exact NNReal.tendsto_coe.mpr
      (avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero (n : ℝ≥0))
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
  filter_upwards [hCell, hSource] with ω hc hS
  let Z : ℕ → ℕ → ℝ := fun m i =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
  let H : ℕ → ℕ → ℝ := fun m i =>
    Real.exp (-(q * (s m i : ℝ))) *
      (deriv w (x + X.X (s m i) ω - rightLimit D (s m i) ω) * Z m i +
        (iteratedDeriv 2 w
          (x + X.X (s m i) ω - rightLimit D (s m i) ω) / 2) *
          ((Z m i)^2 - (Δ m : ℝ) * X.σ^2)) +
      (Δ m : ℝ) * Real.exp (-(q * (s m i : ℝ))) *
        X.generator w (x + X.X (s m i) ω - rightLimit D (s m i) ω)
  have hBound (m i : ℕ) (hi : i < m) (hm : CrossMask m i ω) :
      |H m i| ≤ K * (|Z m i| + (Z m i)^2 + (Δ m : ℝ)) := by
    have h := hc m i hm.1
    simpa only [H, Z, s, Δ] using h
  have hSourceZ : Tendsto (fun m : ℕ =>
      ∑ i ∈ Finset.range m, if CrossMask m i ω then |Z m i| else 0)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Z,s,Δ] using hS
  have hlim :=
    avram_ga_a417_unique_masked_quadratic_limit_transfer
      (fun m i => CrossMask m i ω) Z H
      (fun m => (Δ m : ℝ)) K hK
      (fun m => (Δ m).property) (hUnique ω) hBound hSourceZ hWidth
  simpa only [Err,H,Z] using hlim
