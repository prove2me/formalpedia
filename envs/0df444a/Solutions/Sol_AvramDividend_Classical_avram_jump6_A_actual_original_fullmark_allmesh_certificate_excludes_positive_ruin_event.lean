-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_original_fullmark_allmesh_certificate_excludes_positive_ruin_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:08:12.902489+00:00
-- url     : https://prove2.me/submissions/7cede231-8107-4f38-b6aa-9fffcf30b288

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (κ : ℕ → Ω → ℝ≥0) (k : ℕ)
    (H : ℕ → Ω → ℝ) (R Jfull : ℝ≥0 → Ω → ℝ)
    (N : Ω → ℕ) (A : Set Ω)
    (hEvent : P.restrict (A ∩ {η : Ω | κ k η ≠ 0}) ≠ 0)
    (hPhysical : ∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})),
      H k ω = 0 ∧ R (κ k ω) ω ≤ 1 / 4000 ∧
      (κ k ω : ℝ) ≤ 1 / 500 ∧ 1 ≤ N ω ∧
      Jfull (κ k ω) ω =
        -2 * (N ω : ℝ) + 2 * (κ k ω : ℝ))
    (hMesh : ∃ B E : ℕ → Ω → ℝ,
      (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})), ∀ m, B m ω ≤ 0) ∧
      (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})),
        Tendsto (fun m => E m ω) atTop (nhds (0 : ℝ))) ∧
      (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})), ∀ m,
        H k ω ≤ (111 / 100 : ℝ) + R (κ k ω) ω +
          Jfull (κ k ω) ω + B m ω + E m ω)) :
    False := by
  obtain ⟨B, E, hB, hE, hCash⟩ := hMesh
  haveI : (ae (P.restrict (A ∩ {η : Ω | κ k η ≠ 0}))).NeBot :=
    ae_neBot.mpr hEvent
  have hAll : ∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})),
      (H k ω = 0 ∧ R (κ k ω) ω ≤ 1 / 4000 ∧
        (κ k ω : ℝ) ≤ 1 / 500 ∧ 1 ≤ N ω ∧
        Jfull (κ k ω) ω =
          -2 * (N ω : ℝ) + 2 * (κ k ω : ℝ)) ∧
      (∀ m, B m ω ≤ 0) ∧
      Tendsto (fun m => E m ω) atTop (nhds (0 : ℝ)) ∧
      (∀ m, H k ω ≤ (111 / 100 : ℝ) + R (κ k ω) ω +
        Jfull (κ k ω) ω + B m ω + E m ω) := by
    filter_upwards [hPhysical, hB, hE, hCash] with ω hp hb he hc
    exact ⟨hp, hb, he, hc⟩
  obtain ⟨ω, ⟨⟨hH, hR, ht, hN, hJ⟩, hBω, hEω, hCω⟩⟩ := hAll.exists
  have hEventually : ∀ᶠ m : ℕ in atTop, E m ω < (1 / 2 : ℝ) :=
    hEω.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨m, hm⟩ := hEventually.exists
  have hn : (1 : ℝ) ≤ (N ω : ℝ) := by exact_mod_cast hN
  have hb := hBω m
  have hc := hCω m
  linarith
