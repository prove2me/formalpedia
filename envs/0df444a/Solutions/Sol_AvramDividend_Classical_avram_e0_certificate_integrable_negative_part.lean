-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_certificate_integrable_negative_part
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-11-07T18:25:30.182387+00:00
-- url     : https://prove2.me/submissions/1d96715a-8964-45c5-8485-6c83dd75a9bc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (F B M E₁ E₂ : Ω → ℝ) (c : ℝ),
      (∀ᵐ ω ∂P, 0 ≤ F ω) →
      Measurable B →
      Integrable M P →
      Integrable E₁ P →
      Integrable E₂ P →
      (∀ᵐ ω ∂P, F ω ≤ c + M ω + B ω + E₁ ω + E₂ ω) →
      Integrable (fun ω => max (-B ω) 0) P) := by
  intro hall
  have hresult : Integrable
      (fun n : ℕ => max (-(-(1 / 2 : ℝ))) 0)
      (Measure.count : Measure ℕ) := by
    refine (hall (Ω := ℕ) (Measure.count : Measure ℕ)
      (fun _ => (0 : ℝ))
      (fun _ => -(1 / 2 : ℝ))
      (fun _ => (0 : ℝ))
      (fun _ => (0 : ℝ))
      (fun _ => (0 : ℝ)) (1 : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall (by intro n; norm_num)
    · exact measurable_const
    · simp
    · simp
    · simp
    · exact Filter.Eventually.of_forall (by intro n; norm_num)
  have hconst : Integrable (fun _ : ℕ => (1 / 2 : ℝ))
      (Measure.count : Measure ℕ) := by
    simpa using hresult
  have hfinite : IsFiniteMeasure (Measure.count : Measure ℕ) :=
    (integrable_const_iff_isFiniteMeasure (by norm_num)).mp hconst
  letI : IsFiniteMeasure (Measure.count : Measure ℕ) := hfinite
  have htop : (Measure.count : Measure ℕ) Set.univ = ⊤ := by simp
  have hlt : (Measure.count : Measure ℕ) Set.univ < ⊤ :=
    measure_lt_top (Measure.count : Measure ℕ) Set.univ
  exact (ne_of_lt hlt) htop
