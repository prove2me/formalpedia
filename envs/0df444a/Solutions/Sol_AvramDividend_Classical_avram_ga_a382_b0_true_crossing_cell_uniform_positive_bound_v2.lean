-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a382_b0_true_crossing_cell_uniform_positive_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:24:55.00281+00:00
-- url     : https://prove2.me/submissions/1682813e-ff49-463c-8d2b-6ad4517a4ba2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a389_original_true_crossing_value_uniform_abs_vanish
import Theorems.Thm_AvramDividend_Classical_avram_ga_a390_original_true_crossing_HJB_uniform_abs_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

private theorem crossing_max_sub_bound (u v : ℝ) :
    max (u - v) 0 ≤ |u| + |v| := by
  apply max_le
  · nlinarith [le_abs_self u, neg_le_abs v]
  · nlinarith [abs_nonneg u, abs_nonneg v]

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
    let F : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let R : ℕ → ℝ := fun k => X.X (s k + Δ) ω - X.X (s k) ω
      let Z : ℕ → ℝ := fun k => R k - (Δ : ℝ) * X.c
      let H : ℕ → ℝ := fun k =>
        E (s k) * (deriv w (Y (s k)) * Z k +
          (iteratedDeriv 2 w (Y (s k)) / 2) *
            (Z k^2 - (Δ : ℝ) * X.σ^2)) +
          (Δ : ℝ) * E (s k) * X.generator w (Y (s k))
      E (ρ ω) * (w (Y (s i) +
        (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i))) - H i
    ∃ B : ℕ → Ω → ℝ,
      (∀ (m : ℕ) (ω : Ω), 0 ≤ B m ω) ∧
      (∀ (m : ℕ) (ω : Ω) (i : ℕ), i < m →
        (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω →
        ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
          max (F m i ω) 0 ≤ B m ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun m => B m ω)
        atTop (nhds (0 : ℝ))) := by
  classical
  intro F
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : Ω → ℝ≥0 → ℝ := fun ω t => x + X.X t ω - rightLimit D t ω
  let Val : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    E (ρ ω) * (w (Y ω (s m i) +
      (X.X (ρ ω) ω - X.X (s m i) ω)) - w (Y ω (s m i)))
  let Hcell : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    let R : ℝ := X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℝ := R - (Δ m : ℝ) * X.c
    E (s m i) * (deriv w (Y ω (s m i)) * Z +
      (iteratedDeriv 2 w (Y ω (s m i)) / 2) *
        (Z^2 - (Δ m : ℝ) * X.σ^2)) +
      (Δ m : ℝ) * E (s m i) * X.generator w (Y ω (s m i))

  obtain ⟨BV, hBV0, hBVb, hBVlim⟩ :=
    avram_ga_a389_original_true_crossing_value_uniform_abs_vanish
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  obtain ⟨BH, hBH0, hBHb, hBHlim⟩ :=
    avram_ga_a390_original_true_crossing_HJB_uniform_abs_vanish
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  refine ⟨(fun m ω => BV m ω + BH m ω), ?_, ?_, ?_⟩
  · intro m ω
    exact add_nonneg (hBV0 m ω) (hBH0 m ω)
  · intro m ω i hi hs he
    have hVal := hBVb m ω i hi hs he
    have hH := hBHb m ω i hi hs he
    have hEq : F m i ω = Val m i ω - Hcell m i ω := rfl
    rw [hEq]
    exact (crossing_max_sub_bound (Val m i ω) (Hcell m i ω)).trans
      (add_le_add hVal hH)
  · filter_upwards [hBVlim, hBHlim] with ω hVal hH
    have hSum : Tendsto (fun m => BV m ω + BH m ω)
        atTop (nhds ((0 : ℝ) + 0)) := by
      convert hVal.add hH using 1 <;> simp
    simpa only [zero_add] using hSum
