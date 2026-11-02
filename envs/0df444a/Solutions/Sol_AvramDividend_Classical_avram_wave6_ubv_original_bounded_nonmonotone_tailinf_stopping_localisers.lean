-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_ubv_original_bounded_nonmonotone_tailinf_stopping_localisers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:57:42.689395+00:00
-- url     : https://prove2.me/submissions/8e9517dd-a863-48eb-8527-65bcaebdc8fe

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_min_liminf_clock_eq
import Theorems.Thm_avram_wave6_monotone_ennreal_diagonal_nat_clip_sup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => min (⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞))) ∧
    (∀ n ω, min (⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞) ≤
      (n : ℝ≥0∞)) ∧
    (∀ ω, Monotone
      (fun n : ℕ => min (⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞))) ∧
    (∀ᵐ ω ∂P,
      (⨆ n : ℕ, min (⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞)) =
      ruinTime X x D ω) := by
  let τ : ℕ → Ω → ℝ≥0∞ :=
    fun n ω => ⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω)
  have hclock := avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
    X x C D hD S hSstop
  have hmono : ∀ ω, Monotone (fun n => τ n ω) := by
    simpa only [τ] using hclock.2.2
  have hsupae : ∀ᵐ ω ∂P, (⨆ n, τ n ω) = ruinTime X x D ω := by
    simpa only [τ] using
      (avram_wave5_ubv_original_ruin_min_liminf_clock_eq X x D S hSliminfAE)
  change
    (∀ n, IsStoppingTime 𝓕.rightCont
      (fun ω => min (τ n ω) (n : ℝ≥0∞))) ∧
    (∀ n ω, min (τ n ω) (n : ℝ≥0∞) ≤ (n : ℝ≥0∞)) ∧
    (∀ ω, Monotone (fun n : ℕ => min (τ n ω) (n : ℝ≥0∞))) ∧
    (∀ᵐ ω ∂P, (⨆ n : ℕ, min (τ n ω) (n : ℝ≥0∞)) =
      ruinTime X x D ω)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact (hclock.1 n).min_const (n : ℝ≥0)
  · intro n ω
    exact min_le_right _ _
  · intro ω i j hij
    apply min_le_min (hmono ω hij)
    exact_mod_cast hij
  · filter_upwards [hsupae] with ω hω
    calc
      (⨆ n : ℕ, min (τ n ω) (n : ℝ≥0∞)) =
          (⨆ n : ℕ, τ n ω) :=
        avram_wave6_monotone_ennreal_diagonal_nat_clip_sup
          (fun n => τ n ω) (hmono ω)
      _ = ruinTime X x D ω := hω
end
