-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.adaptive_fresh_observed
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:40:10.235881+00:00
-- url     : https://prove2.me/submissions/31655166-e6f8-4bdf-a8cc-a31ce5feaebc

import Mathlib
import Theorems.Thm_CountingLLL_ReciprocalTest_fresh_coordinate_event
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem finite_dep_meas {ι : Type*} [DecidableEq ι] (S : Finset ι) (E : Set (ι → Bool))
    (hE : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)) : MeasurableSet E := by
  classical
  let f : (ι → Bool) → (S → Bool) := fun ω j => ω j
  have hf : Measurable f := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (S → Bool) := {x | ∃ ω : ι → Bool, f ω = x ∧ ω ∈ E}
  have heq : f ⁻¹' F = E := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      apply (hE ω ω' ?_).2 hn
      intro i hi
      exact (congrFun heq ⟨i,hi⟩).symm
    · intro hn; exact ⟨ω, rfl, hn⟩
  rw [← heq]
  exact MeasurableSet.of_discrete.preimage hf

/-- A nonanticipating finite reveal rule selects a fresh unbiased coordinate. -/
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (κ : ι → Measure Bool) [∀ i, IsProbabilityMeasure (κ i)] (p : ℝ≥0∞)
    (revealed : (ι → Bool) → Finset ι) (next : (ι → Bool) → ι)
    (hfresh : ∀ ω, next ω ∉ revealed ω)
    (hsame : ∀ ω, κ (next ω) {true} = p)
    (E : Set (ι → Bool))
    (hlocal : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      ((revealed ω = S ∧ next ω = a) ↔ (revealed ω' = S ∧ next ω' = a)))
    (hobserved : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      (revealed ω = S ∧ next ω = a) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω (next ω) = true} =
      (Measure.infinitePi κ) E * p := by
  classical
  let μ := Measure.infinitePi κ
  let C : (Finset ι × ι) → Set (ι → Bool) := fun x => {ω | ω ∈ E ∧ revealed ω = x.1 ∧ next ω = x.2}
  have hClocal (x : Finset ι × ι) : ∀ ω ω', (∀ i ∈ x.1, ω i = ω' i) → (ω ∈ C x ↔ ω' ∈ C x) := by
    intro ω ω' h
    have hc := hlocal x.1 x.2 ω ω' h
    constructor
    · rintro ⟨he, hr, hn⟩
      exact ⟨(hobserved x.1 x.2 ω ω' h ⟨hr,hn⟩).1 he, hc.1 ⟨hr,hn⟩⟩
    · rintro ⟨he, hr, hn⟩
      have hclass := hc.2 ⟨hr,hn⟩
      exact ⟨(hobserved x.1 x.2 ω ω' h hclass).2 he, hclass⟩
  have hCmeas (x : Finset ι × ι) : MeasurableSet (C x) :=
    finite_dep_meas x.1 (C x) (hClocal x)
  have hCdisj : Pairwise (fun x y => Disjoint (C x) (C y)) := by
    intro x y hxy
    apply Set.disjoint_left.mpr
    intro ω hx hy
    have he : x = y := by
      apply Prod.ext
      · exact hx.2.1.symm.trans hy.2.1
      · exact hx.2.2.symm.trans hy.2.2
    exact hxy he
  have hCcover : (⋃ x, C x) = E := by
    ext ω
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx⟩; exact hx.1
    · intro he; exact ⟨(revealed ω,next ω), he, rfl, rfl⟩
  let D : (Finset ι × ι) → Set (ι → Bool) := fun x => C x ∩ {ω | ω x.2 = true}
  have hDmeas (x : Finset ι × ι) : MeasurableSet (D x) :=
    (hCmeas x).inter ((MeasurableSet.singleton true).preimage (measurable_pi_apply x.2))
  have hDdisj : Pairwise (fun x y => Disjoint (D x) (D y)) := by
    intro x y hxy
    exact (hCdisj hxy).mono Set.inter_subset_left Set.inter_subset_left
  have hDcover : (⋃ x, D x) = {ω | ω ∈ E ∧ ω (next ω) = true} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, hxbit⟩
      exact ⟨hx.1, by simpa [hx.2.2] using hxbit⟩
    · rintro ⟨he,hbit⟩
      exact ⟨(revealed ω,next ω), ⟨he,rfl,rfl⟩, hbit⟩
  have hfactor (x : Finset ι × ι) : μ (D x) = μ (C x) * p := by
    by_cases ha : x.2 ∈ x.1
    · have hempty : C x = ∅ := by
        ext ω
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hω
        have hh := hfresh ω
        rw [hω.2.1,hω.2.2] at hh
        exact hh ha
      simp [D, hempty]
    · by_cases he : C x = ∅
      · simp [D, he]
      · obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr he
        have hx : κ x.2 {true} = p := by simpa [hω.2.2] using hsame ω
        rw [← hx]
        exact CountingLLL.ReciprocalTest.fresh_coordinate_event κ x.1 x.2 ha (C x) (hClocal x)
  calc
    μ {ω | ω ∈ E ∧ ω (next ω) = true} = μ (⋃ x, D x) := by rw [hDcover]
    _ = ∑' x, μ (D x) := measure_iUnion hDdisj hDmeas
    _ = ∑' x, μ (C x) * p := by simp_rw [hfactor]
    _ = (∑' x, μ (C x)) * p := ENNReal.tsum_mul_right
    _ = μ (⋃ x, C x) * p := by rw [measure_iUnion hCdisj hCmeas]
    _ = μ E * p := by rw [hCcover]
