-- Prove2me | solution 1 for AvramDividend.Classical.avram_b249_original_ruinclipped_physical_postpayment_discount_gap_bounded_dividend_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:36:12.9902+00:00
-- url     : https://prove2.me/submissions/626c1c54-5f26-4d03-8ceb-d456c7cb788d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ) (hLip :
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |w s - w t| ≤ L * |s - t|)
    (σ : Ω → ℝ≥0) (n m : ℕ)
    (hmesh : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      ((v (i + 1) : ℝ) - (v i : ℝ)) ≤ (Δ : ℝ))
    (hPre : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ∈ Icc a b)
    (hPost : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω ∈ Icc a b) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    (∑ i ∈ Finset.range m,
      (Real.exp (-(q * (v i : ℝ))) -
       Real.exp (-(q * (v (i + 1) : ℝ)))) *
      |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
       w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|) ≤
    q * (Δ : ℝ) * L *
      (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i =>
    min ((i : ℝ≥0) * Δ) (σ ω)
  have hvMono : Monotone v := by
    intro i j hij
    dsimp [v]
    gcongr
  have h := avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
    X x D hD ω q hq w L hL a b hLip v hvMono m (Δ : ℝ)
    (by positivity) hmesh hPre hPost
  exact h
