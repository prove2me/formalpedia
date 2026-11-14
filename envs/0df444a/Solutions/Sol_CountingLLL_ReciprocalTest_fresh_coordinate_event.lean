-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.fresh_coordinate_event
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:36:53.267836+00:00
-- url     : https://prove2.me/submissions/5fb224ab-ee31-4817-ac6c-4181d4a2fc71

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- An unrevealed coordinate is independent of any event determined by finitely many others. -/
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (κ : ι → Measure Bool) [∀ i, IsProbabilityMeasure (κ i)]
    (S : Finset ι) (a : ι) (ha : a ∉ S) (E : Set (ι → Bool))
    (hE : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω a = true} =
      (Measure.infinitePi κ) E * κ a {true} := by
  classical
  let μ := Measure.infinitePi κ
  let Q : Finset ι := {a}
  let f : (ι → Bool) → (S → Bool) := fun ω j => ω j
  let g : (ι → Bool) → (Q → Bool) := fun ω j => ω j
  have disj : Disjoint S Q := by simp [Q, Finset.disjoint_left, ha]
  have hind : iIndepFun (fun i (ω : ι → Bool) => ω i) μ := iIndepFun_infinitePi (fun _ => measurable_id)
  have hi := iIndepFun.indepFun_finset S Q disj hind (fun i => measurable_pi_apply i)
  let F : Set (S → Bool) := {x | ∃ ω : ι → Bool, f ω = x ∧ ω ∈ E}
  let G : Set (Q → Bool) := {x | x ⟨a, by simp [Q]⟩ = true}
  have hF : MeasurableSet F := MeasurableSet.of_discrete
  have hG : MeasurableSet G := MeasurableSet.of_discrete
  have hpre : f ⁻¹' F = E := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      have he : ∀ i ∈ S, ω i = ω' i := by
        intro i hi
        exact (congrFun heq ⟨i,hi⟩).symm
      exact (hE ω ω' he).2 hn
    · intro hn; exact ⟨ω, rfl, hn⟩
  have hgpre : g ⁻¹' G = {ω : ι → Bool | ω a = true} := by ext ω; rfl
  have hmass : μ {ω : ι → Bool | ω a = true} = κ a {true} := by
    have hmap : μ.map (fun ω => ω a) = κ a := Measure.infinitePi_map_eval _ _
    change μ ((fun ω : ι → Bool => ω a) ⁻¹' ({true} : Set Bool)) = _
    rw [← Measure.map_apply (measurable_pi_apply a) (MeasurableSet.singleton true), hmap]
  have hcalc := hi.measure_inter_preimage_eq_mul F G hF hG
  rw [hpre, hgpre, hmass] at hcalc
  exact hcalc
