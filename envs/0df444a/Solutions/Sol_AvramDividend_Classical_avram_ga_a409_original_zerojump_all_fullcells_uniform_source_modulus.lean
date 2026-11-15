-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:27:13.754036+00:00
-- url     : https://prove2.me/submissions/565406ea-e718-47cc-b027-b407f8a125a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a406_uniform_continuous_finite_mesh_oscillation
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option maxHeartbeats 800000

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          |X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
                 ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
            X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω| < ε := by
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let t : ℕ → ℕ → ℝ≥0 := fun m i => s m i + Δ m
  have hEnd (m i : ℕ) (hi : i < m) : t m i ≤ (n : ℝ≥0) := by
    have hidx : (i : ℝ≥0) + 1 ≤ (m : ℝ≥0) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hi)
    calc
      t m i = ((i : ℝ≥0) + 1) * Δ m := by
        dsimp [t, s]
        ring
      _ ≤ ((m : ℝ≥0) + 1) * Δ m := mul_le_mul_of_nonneg_right hidx (bot_le)
      _ = n := by
        dsimp [Δ]
        field_simp
  have hR (m i : ℕ) (hi : i < m) :
      s m i ∈ Icc 0 (n : ℝ≥0) ∧ t m i ∈ Icc 0 (n : ℝ≥0) := by
    have he := hEnd m i hi
    exact ⟨⟨bot_le, (le_add_of_nonneg_right (bot_le)).trans he⟩,
      ⟨bot_le, he⟩⟩
  have hG (m i : ℕ) (_ : i < m) :
      dist (s m i) (t m i) ≤ (n : ℝ≥0) / ((m : ℝ≥0) + 1) := by
    change dist (s m i) (s m i + Δ m) ≤ (Δ m : ℝ)
    rw [NNReal.dist_eq, NNReal.coe_add]
    have hs : (s m i : ℝ) - ((s m i : ℝ) + (Δ m : ℝ)) ≤ 0 := by
      have hd : 0 ≤ (Δ m : ℝ) := (Δ m).property
      linarith
    rw [abs_of_nonpos hs]
    simp
  filter_upwards
    [avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
      X hν (n : ℝ≥0)] with ω hUC
  have hosc := avram_ga_a406_uniform_continuous_finite_mesh_oscillation
    (fun v : ℝ≥0 => X.X v ω) (n : ℝ≥0) hUC s t hR hG
  intro ε hε
  obtain ⟨k, hk⟩ := hosc ε hε
  refine ⟨k, ?_⟩
  intro m hm i hi
  have hh := hk m hm i hi
  dsimp [s, t, Δ] at hh
  simpa only [Real.dist_eq, abs_sub_comm] using hh
