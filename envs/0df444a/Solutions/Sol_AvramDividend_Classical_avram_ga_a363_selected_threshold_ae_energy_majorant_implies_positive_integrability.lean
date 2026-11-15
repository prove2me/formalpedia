-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a363_selected_threshold_ae_energy_majorant_implies_positive_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:10:37.570167+00:00
-- url     : https://prove2.me/submissions/3b50dbf9-42af-4e81-8d73-c6e9d124eeab

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℝ → ℕ → Ω → ℝ) (E A B : ℕ → Ω → ℝ)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hSm : ∀ m, AEStronglyMeasurable
      (fun ω => max (S δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hAI : ∀ m, Integrable (A m) P)
    (hBI : ∀ m, Integrable (B m) P)
    (hPt : ∀ m, ∀ᵐ ω ∂P,
      max (S δ m ω) 0 ≤ ε * E m ω + A m ω + B m ω) :
    ∀ m, Integrable (fun ω => max (S δ m ω) 0) P := by
  intro m
  have hMajor : Integrable
      (fun ω => ε * E m ω + A m ω + B m ω) P :=
    (((hEI m).const_mul ε).add (hAI m)).add (hBI m)
  apply Integrable.mono' hMajor (hSm m)
  filter_upwards [hPt m] with ω h
  have hPos : 0 ≤ ε * E m ω + A m ω + B m ω :=
    (le_max_right (S δ m ω) (0 : ℝ)).trans h
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (le_max_right (S δ m ω) (0 : ℝ)),
    abs_of_nonneg hPos] using h
