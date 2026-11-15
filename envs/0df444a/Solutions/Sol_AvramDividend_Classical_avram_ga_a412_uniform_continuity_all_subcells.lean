-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a412_uniform_continuity_all_subcells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:25:46.473555+00:00
-- url     : https://prove2.me/submissions/e7f76022-25f0-452d-8b42-16c177ee5ed2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Metric Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : UniformContinuousOn f (Icc 0 T))
    (s : ℕ → ℕ → ℝ≥0) (Δ : ℕ → ℝ≥0)
    (hEnd : ∀ m i : ℕ, i < m → s m i + Δ m ≤ T)
    (hWidth : ∀ m : ℕ, Δ m ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∀ i : ℕ, i < m →
        ∀ u : ℝ≥0, s m i ≤ u → u ≤ s m i + Δ m →
          dist (f (s m i)) (f u) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hf) ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt ((T : ℝ) / δ)
  refine ⟨k, ?_⟩
  intro m hm i hi u hsu hu
  have hmReal : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq : (T : ℝ) / δ < (m : ℝ) + 1 := by linarith
  have hmul : (T : ℝ) < δ * ((m : ℝ) + 1) := by
    have h := (div_lt_iff₀ hδ).mp hq
    nlinarith
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hwidth : ((T / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) < δ := by
    rw [NNReal.coe_div]
    push_cast
    exact (div_lt_iff₀ hden).mpr (by nlinarith)
  have hΔsmall : (Δ m : ℝ) < δ :=
    lt_of_le_of_lt (by exact_mod_cast hWidth m) hwidth
  have hsEnd := hEnd m i hi
  have hsR : s m i ∈ Icc 0 T :=
    ⟨bot_le, (le_add_of_nonneg_right bot_le).trans hsEnd⟩
  have huR : u ∈ Icc 0 T := ⟨bot_le, hu.trans hsEnd⟩
  have hGap : dist (s m i) u ≤ (Δ m : ℝ) := by
    rw [NNReal.dist_eq]
    have hs : (s m i : ℝ) ≤ (u : ℝ) := by exact_mod_cast hsu
    rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    have ht : (u : ℝ) ≤ (s m i : ℝ) + (Δ m : ℝ) := by
      exact_mod_cast hu
    linarith
  exact hmod (s m i) hsR u huR (hGap.trans_lt hΔsmall)
