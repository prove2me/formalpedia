-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a414_zerojump_inclusive_crossing_subcell_raw_uniform_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:31:05.750303+00:00
-- url     : https://prove2.me/submissions/c8f0efb7-c5d6-41c8-ba92-88cc447cb8dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a412_uniform_continuity_all_subcells
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option maxHeartbeats 800000

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          s < ρ ω → ρ ω ≤ s + Δ →
            |X.X (ρ ω) ω - X.X s ω| < ε := by
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  have hEnd (m i : ℕ) (hi : i < m) : s m i + Δ m ≤ (n : ℝ≥0) := by
    have hidx : (i : ℝ≥0) + 1 ≤ (m : ℝ≥0) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hi)
    calc
      s m i + Δ m = ((i : ℝ≥0) + 1) * Δ m := by
        dsimp [s]
        ring
      _ ≤ ((m : ℝ≥0) + 1) * Δ m := mul_le_mul_of_nonneg_right hidx bot_le
      _ = n := by dsimp [Δ]; field_simp
  have hWidth (m : ℕ) : Δ m ≤ (n : ℝ≥0) / ((m : ℝ≥0) + 1) := le_refl _
  filter_upwards
    [avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
      X hν (n : ℝ≥0)] with ω hUC
  have hosc := avram_ga_a412_uniform_continuity_all_subcells
    (fun v : ℝ≥0 => X.X v ω) (n : ℝ≥0) hUC s Δ hEnd hWidth
  intro ε hε
  obtain ⟨k, hk⟩ := hosc ε hε
  refine ⟨k, ?_⟩
  intro m hm i hi Δ' s' hs ht
  have h := hk m hm i hi (ρ ω) (le_of_lt hs) ht
  simpa only [s, Δ, Real.dist_eq, abs_sub_comm] using h
