-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB216_original_selected_clipped_L2_all_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:22:39.926123+00:00
-- url     : https://prove2.me/submissions/88e09923-e631-4ced-938e-68b5dfc30ff4

import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB207_original_selected_clipped_mesh_L2_for_countable_horizons
import Theorems.Thm_AvramDividend_Classical_avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original controlled reserve selected-band stopped L2 mesh convergence. -/
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
        Tendsto (fun m : ℕ =>
          ∫ t in Ioo (0 : ℝ) ((n k : ℕ) : ℝ),
            (∫ ω, (K a b k m t ω - H a b k t ω)^2 ∂P)
            ∂volume) atTop (𝓝 (0 : ℝ)) := by
  intro Y K H
  have hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2) := by
    simpa only [Y] using
      (avram_wave8_20_original_postpayment_reserve_joint_measurable
        X x D hD)
  have hAll (a : ℝ) (ha' : a ∈ Ioo alo ahi)
      (b : ℝ) (hb' : b ∈ Ioo blo bhi) (k : ℕ) :
      (∀ m, Measurable (fun z : ℝ × Ω => K a b k m z.1 z.2)) ∧
      Measurable (fun z : ℝ × Ω => H a b k z.1 z.2) ∧
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ m t ω, t ∈ Ioo (0 : ℝ) ((n k : ℕ) : ℝ) →
          |K a b k m t ω| ≤ B) ∧
        (∀ t ω, t ∈ Ioo (0 : ℝ) ((n k : ℕ) : ℝ) →
          |H a b k t ω| ≤ B) := by
    have hc : ContinuousOn (deriv w) (Icc a b) := by
      intro y hy
      have hy' : y ∈ Ioo alo bhi :=
        ⟨lt_of_lt_of_le ha'.1 hy.1, lt_of_le_of_lt hy.2 hb'.2⟩
      exact (hDeriv y hy').continuousWithinAt
    have hh :=
      avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
        Y hY (ρ k) (hρ k) w a b hc q (le_of_lt hq) (n k) (hn k)
    simpa only [K, H, Real.toNNReal_coe, NNReal.coe_lt_coe] using hh
  apply (avram_gbB207_original_selected_clipped_mesh_L2_for_countable_horizons
    X hν x D hD n hn ρ q w alo ahi blo bhi ha hSep hb hDeriv)
  · intro a ha' b hb' k m
    exact (hAll a ha' b hb' k).1 m
  · intro a ha' b hb' k
    exact (hAll a ha' b hb' k).2.1
  · intro a ha' b hb' k
    obtain ⟨B, hB, hKb, hHb⟩ := (hAll a ha' b hb' k).2.2
    exact ⟨B, B, hB, hB, hKb, hHb⟩

