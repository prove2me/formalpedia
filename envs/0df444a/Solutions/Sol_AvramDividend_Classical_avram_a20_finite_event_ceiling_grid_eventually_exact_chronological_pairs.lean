-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_event_ceiling_grid_eventually_exact_chronological_pairs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:36:37.350083+00:00
-- url     : https://prove2.me/submissions/0044a862-3995-4c3e-b68b-47b6584bac4d

import Mathlib.Data.Finset.Defs
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_event_uniform_mesh_positive_pair_gap
import Theorems.Thm_AvramDividend_Classical_avram_a20_positive_mesh_time_gap_implies_strict_ceiling_order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (F : Finset ℝ≥0) (T : ℝ≥0) (hT : 0 < T) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))) := by
  classical
  obtain ⟨k₀, hk₀, hGap⟩ :=
    avram_a20_finite_event_uniform_mesh_positive_pair_gap F T
  refine ⟨k₀, hk₀, ?_⟩
  intro k hk
  have hScale (u v : ℝ≥0) (hu : u ∈ F) (hv : v ∈ F)
      (huv : u < v) :
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) <
      Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) :=
    avram_a20_positive_mesh_time_gap_implies_strict_ceiling_order
      u v T hT k (hGap k hk u hu v hv huv)
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    exact ⟨⟨ha, hb⟩, hScale p.1 p.2 ha hb hab⟩
  · rintro ⟨⟨ha, hb⟩, hab⟩
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · exact ⟨⟨ha, hb⟩, hlt⟩
    · simp [heq] at hab
    · exact False.elim (lt_asymm hab (hScale p.2 p.1 hb ha hgt))
