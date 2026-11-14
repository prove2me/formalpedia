-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.fresh_coordinate_event_general
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:40:11.023875+00:00
-- url     : https://prove2.me/submissions/48de58b0-ef96-43dd-acae-f68527d65167

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- An unrevealed coordinate is independent of any event determined by finitely many others. -/
theorem solution {ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (S : Finset ι) (a : ι) (ha : a ∉ S) (E : Set (ι → α))
    (hE : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω a ∈ A a} =
      (Measure.infinitePi κ) E * κ a (A a) := by
  classical
  let μ := Measure.infinitePi κ
  let Q : Finset ι := {a}
  let f : (ι → α) → (S → α) := fun ω j => ω j
  let g : (ι → α) → (Q → α) := fun ω j => ω j
  have disj : Disjoint S Q := by simp [Q, Finset.disjoint_left, ha]
  have hind : iIndepFun (fun i (ω : ι → α) => ω i) μ := iIndepFun_infinitePi (fun _ => measurable_id)
  have hi := iIndepFun.indepFun_finset S Q disj hind (fun i => measurable_pi_apply i)
  let F : Set (S → α) := {x | ∃ ω : ι → α, f ω = x ∧ ω ∈ E}
  let G : Set (Q → α) := {x | x ⟨a, by simp [Q]⟩ ∈ A a}
  have hF : MeasurableSet F := (Set.to_countable F).measurableSet
  have hG : MeasurableSet G := (hA a).preimage (measurable_pi_apply (⟨a, by simp [Q]⟩ : Q))
  have hpre : f ⁻¹' F = E := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      have he : ∀ i ∈ S, ω i = ω' i := by
        intro i hi
        exact (congrFun heq ⟨i,hi⟩).symm
      exact (hE ω ω' he).2 hn
    · intro hn; exact ⟨ω, rfl, hn⟩
  have hgpre : g ⁻¹' G = {ω : ι → α | ω a ∈ A a} := by ext ω; rfl
  have hmass : μ {ω : ι → α | ω a ∈ A a} = κ a (A a) := by
    have hmap : μ.map (fun ω => ω a) = κ a := Measure.infinitePi_map_eval _ _
    change μ ((fun ω : ι → α => ω a) ⁻¹' (A a)) = _
    rw [← Measure.map_apply (measurable_pi_apply a) (hA a), hmap]
  have hcalc := hi.measure_inter_preimage_eq_mul F G hF hG
  rw [hpre, hgpre, hmass] at hcalc
  exact hcalc
