-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB220_original_selected_clipped_two_mesh_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:14.066582+00:00
-- url     : https://prove2.me/submissions/f0885a2d-70b8-45f9-84ad-c81ce6d27ae4

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB216_original_selected_clipped_L2_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_gbB219_interval_bounded_one_mesh_L2_implies_two_mesh_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Genuine controlled Gaussian selected clipping yields two-mesh L2 Cauchy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (ρ : ℕ → Ω → ℝ≥0) (hρ : ∀ k, Measurable (ρ k))
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (alo ahi blo bhi : ℝ) (ha : alo < ahi)
    (hSep : ahi < blo) (hb : blo < bhi)
    (hDeriv : ∀ y ∈ Ioo alo bhi, ContinuousAt (deriv w) y) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    let K : ℝ → ℝ → ℕ → ℕ → ℝ → Ω → ℝ := fun a b k m t ω =>
      let Δ : ℝ≥0 := ((n k : ℕ) : ℝ≥0) /
        ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ) then
          if (s : ℝ) < (ρ k ω : ℝ) then
            Real.exp (-(q * (s : ℝ))) *
              (if Y (Real.toNNReal (s : ℝ)) ω ∈ Icc a b
                then deriv w (Y (Real.toNNReal (s : ℝ)) ω)
                else 1)
          else 0
        else 0)
    let H : ℝ → ℝ → ℕ → ℝ → Ω → ℝ := fun a b k t ω =>
      if t < (ρ k ω : ℝ) then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b
            then deriv w (Y (Real.toNNReal t) ω)
            else 1)
      else 0
    ∃ a ∈ Ioo alo ahi, ∃ b ∈ Ioo blo bhi,
      ∀ k : ℕ,
        Tendsto (fun mp : ℕ × ℕ =>
          ∫ t in Ioo (0 : ℝ) ((n k : ℕ) : ℝ),
            (∫ ω, (K a b k mp.1 t ω - K a b k mp.2 t ω)^2 ∂P)
            ∂volume) atTop (𝓝 (0 : ℝ)) := by
  intro Y K H
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨a, haGood, b, hbGood, hL2⟩ :=
    avram_gbB216_original_selected_clipped_L2_all_horizons
      X hν x D hD n hn ρ hρ q hq w alo ahi blo bhi ha hSep hb hDeriv
  have hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2) := by
    simpa only [Y] using
      (avram_wave8_20_original_postpayment_reserve_joint_measurable X x D hD)
  refine ⟨a, haGood, b, hbGood, ?_⟩
  intro k
  have hc : ContinuousOn (deriv w) (Icc a b) := by
    intro y hy
    have hy' : y ∈ Ioo alo bhi := ⟨lt_of_lt_of_le haGood.1 hy.1, lt_of_le_of_lt hy.2 hbGood.2⟩
    exact (hDeriv y hy').continuousWithinAt
  have hAll :
      (∀ m, Measurable (fun z : ℝ × Ω => K a b k m z.1 z.2)) ∧
      Measurable (fun z : ℝ × Ω => H a b k z.1 z.2) ∧
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ m t ω, t ∈ Ioo (0 : ℝ) ((n k : ℕ) : ℝ) → |K a b k m t ω| ≤ B) ∧
        (∀ t ω, t ∈ Ioo (0 : ℝ) ((n k : ℕ) : ℝ) → |H a b k t ω| ≤ B) := by
    have hh :=
      avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
        Y hY (ρ k) (hρ k) w a b hc q (le_of_lt hq) (n k) (hn k)
    simpa only [K, H, Real.toNNReal_coe, NNReal.coe_lt_coe] using hh
  obtain ⟨hKm, hHm, B, hB, hKb, hHb⟩ := hAll
  exact avram_gbB219_interval_bounded_one_mesh_L2_implies_two_mesh_cauchy
    P (n k) (hn k) (K a b k) (H a b k)
    hKm hHm B B hB hB hKb hHb (hL2 k)
