-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger155_original_gaussian_postpayment_HJB_grid_uniform_absolute_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:35:40.71022+00:00
-- url     : https://prove2.me/submissions/ba530b02-6d8f-4ceb-8b67-f1950bc35de6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger157_original_postpayment_compact_generator_uniform_pointwise_abs_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger158_finite_original_discounted_generator_grid_uniform_sum_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation)
    (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let G : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) * (X.generator w y - q * w y)
        else 0)
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ᵐ ω ∂P, |G m ω| ≤ K := by
  intro G
  obtain ⟨B, hB, hPath⟩ :=
    avram_gledger157_original_postpayment_compact_generator_uniform_pointwise_abs_bound
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  refine ⟨(n : ℝ) * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro m
  filter_upwards [hPath] with ω hω
  let δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  have hδ : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg _
  have hδeq : (δ : ℝ) = (n : ℝ) / ((m : ℝ) + 1) := by
    dsimp [δ]
    norm_num [NNReal.coe_div, NNReal.coe_add]
  have hmesh : (m : ℝ) * (δ : ℝ) ≤ (n : ℝ) := by
    rw [hδeq]
    have hd : 0 < (m : ℝ) + 1 := by positivity
    calc
      (m : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) =
          ((m : ℝ) * (n : ℝ)) / ((m : ℝ) + 1) := by ring
      _ ≤ (n : ℝ) := (div_le_iff₀ hd).mpr (by
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith)
  let F : ℕ → ℝ := fun i =>
    let s : ℝ≥0 := (i : ℝ≥0) * δ
    if s < ρ ω then
      Real.exp (-(q * (s : ℝ))) *
        (X.generator w (x + X.X s ω - rightLimit D s ω) -
          q * w (x + X.X s ω - rightLimit D s ω))
    else 0
  have hF : ∀ i ∈ Finset.range m, |F i| ≤ B := by
    intro i hi
    dsimp [F]
    split_ifs with hs
    · have hp := hω _ hs
      have hpos : 0 ≤ Real.exp (-(q * (((i : ℝ≥0) * δ : ℝ)))) :=
        (Real.exp_pos _).le
      have hle : Real.exp (-(q * (((i : ℝ≥0) * δ : ℝ)))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg (le_of_lt hq) (by positivity)))
      rw [abs_mul, abs_of_nonneg hpos]
      calc
        _ ≤ Real.exp (-(q * (((i : ℝ≥0) * δ : ℝ)))) * B :=
          mul_le_mul_of_nonneg_left hp hpos
        _ ≤ B := by nlinarith [mul_nonneg (sub_nonneg.mpr hle) hB]
    · simpa using hB
  have heq : G m ω = Finset.sum (Finset.range m)
      (fun i => (δ : ℝ) * F i) := by
    dsimp [G, F, δ]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [heq]
  exact avram_gledger158_finite_original_discounted_generator_grid_uniform_sum_bound
    m n (δ : ℝ) B hδ hB hmesh F hF

