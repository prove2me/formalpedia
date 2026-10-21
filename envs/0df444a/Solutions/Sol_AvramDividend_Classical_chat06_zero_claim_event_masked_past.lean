-- Prove2me | solution 1 for AvramDividend.Classical.chat06_zero_claim_event_masked_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:04:55.057337+00:00
-- url     : https://prove2.me/submissions/18cb7526-7eef-44e8-988b-e6c96235af7d

import Mathlib.MeasureTheory.Constructions.Pi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

namespace AvramChat06

/-- For a repaired arrival count, the zero-claim event is
almost surely a measurable event of the first waiting time.
Embedding its observed past in the fixed product type ℕ→ℝ
does not reveal any unobserved future coordinates. -/
theorem zero_count_event_ae_masked_past
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ) (t : ℝ)
    (hZero : (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω => t < τ 0 ω)) :
    ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
        (fun ω : Ω =>
          (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S) := by
  let S : Set (ℕ → ℝ) := {g | t < g 0}
  have hS : MeasurableSet S :=
    (measurable_pi_apply (0 : ℕ)) measurableSet_Ioi
  refine ⟨S, hS, ?_⟩
  filter_upwards [hZero] with ω hω
  apply propext
  have hE : (t < τ 0 ω) ↔
      (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S := by
    simp [S]
  exact (Iff.of_eq hω).trans hE

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ) (t : ℝ)
    (hZero : (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω => t < τ 0 ω)) :
    ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
        (fun ω : Ω =>
          (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S) := by
  exact zero_count_event_ae_masked_past τ N t hZero
