-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_generic_joint_law_of_right_ray_rectangles
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-11-11T22:15:52.738238+00:00
-- url     : https://prove2.me/submissions/e397c9af-0f1d-4f6d-81be-28f4871c6f49

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-- Right-ray rectangles with nonnegative thresholds miss the boundary at zero. -/
theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (R U : Ω → ℝ) (F G : Ω → (ℕ → ℝ)),
      AEMeasurable (fun ω => (R ω, F ω)) P →
      AEMeasurable (fun ω => (U ω, G ω)) P →
      (∀ᵐ ω ∂P, 0 ≤ R ω) →
      (∀ᵐ ω ∂P, 0 ≤ U ω) →
      (∀ t : ℝ, 0 ≤ t →
        ∀ B : Set (ℕ → ℝ), MeasurableSet B →
        P {ω | t < R ω ∧ F ω ∈ B} =
          P {ω | t < U ω ∧ G ω ∈ B}) →
      IdentDistrib (fun ω => (R ω, F ω))
        (fun ω => (U ω, G ω)) P P) := by
  classical
  intro h
  let Ω' : Type := PUnit
  letI : MeasurableSpace Ω' := ⊥
  let P : Measure Ω' := Measure.dirac PUnit.unit
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  let R : Ω' → ℝ := fun _ => 0
  let U : Ω' → ℝ := fun _ => 0
  let F : Ω' → (ℕ → ℝ) := fun _ _ => 0
  let G : Ω' → (ℕ → ℝ) := fun _ _ => 1
  have hr : AEMeasurable (fun ω => (R ω, F ω)) P := by
    exact (show Measurable (fun ω : Ω' => (R ω, F ω)) from
      by fun_prop).aemeasurable
  have hu : AEMeasurable (fun ω => (U ω, G ω)) P := by
    exact (show Measurable (fun ω : Ω' => (U ω, G ω)) from
      by fun_prop).aemeasurable
  have hRp : ∀ᵐ ω ∂P, 0 ≤ R ω :=
    Filter.Eventually.of_forall (fun _ => by norm_num [R])
  have hUp : ∀ᵐ ω ∂P, 0 ≤ U ω :=
    Filter.Eventually.of_forall (fun _ => by norm_num [U])
  have hrect : ∀ t : ℝ, 0 ≤ t →
      ∀ B : Set (ℕ → ℝ), MeasurableSet B →
      P {ω | t < R ω ∧ F ω ∈ B} =
        P {ω | t < U ω ∧ G ω ∈ B} := by
    intro t ht B hB
    have hn : ¬ t < (0 : ℝ) := not_lt.mpr ht
    simp [R, U, hn]
  have hid := h (Ω := Ω') P R U F G hr hu hRp hUp hrect
  let p0 : ℝ × (ℕ → ℝ) := ((0 : ℝ), fun _ => (0 : ℝ))
  let p1 : ℝ × (ℕ → ℝ) := ((0 : ℝ), fun _ => (1 : ℝ))
  have hmap : Measure.dirac p0 = Measure.dirac p1 := by
    simpa [P, R, U, F, G, p0, p1] using hid.map_eq
  have hneq : p0 ≠ p1 := by
    intro he
    have hc := congrArg (fun p : ℝ × (ℕ → ℝ) => p.2 0) he
    norm_num [p0, p1] at hc
  exact hneq (MeasureTheory.dirac_eq_dirac_iff.mp hmap)
