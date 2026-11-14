-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.adaptive_fresh_on_event
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:31.621409+00:00
-- url     : https://prove2.me/submissions/f75241cd-63a0-4e83-84d6-d301516f9492

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem fresh_coordinate_event_general {ι α : Type*} [Countable ι] [DecidableEq ι]
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

private theorem finite_dep_meas {ι α : Type*} [DecidableEq ι] [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] (S : Finset ι) (E : Set (ι → α))
    (hE : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)) : MeasurableSet E := by
  classical
  let f : (ι → α) → (S → α) := fun ω j => ω j
  have hf : Measurable f := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (S → α) := {x | ∃ ω : ι → α, f ω = x ∧ ω ∈ E}
  have heq : f ⁻¹' F = E := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      apply (hE ω ω' ?_).2 hn
      intro i hi
      exact (congrFun heq ⟨i,hi⟩).symm
    · intro hn; exact ⟨ω, rfl, hn⟩
  rw [← heq]
  exact (Set.to_countable F).measurableSet.preimage hf

/-- A nonanticipating finite reveal rule selects a fresh unbiased coordinate. -/
theorem solution {ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (p : ℝ≥0∞)
    (revealed : (ι → α) → Finset ι) (next : (ι → α) → ι)
    (E : Set (ι → α))
    (hfresh : ∀ ω, ω ∈ E → next ω ∉ revealed ω)
    (hsame : ∀ ω, ω ∈ E → κ (next ω) (A (next ω)) = p)
    (hlocal : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      ((revealed ω = S ∧ next ω = a) ↔ (revealed ω' = S ∧ next ω' = a)))
    (hobserved : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      (revealed ω = S ∧ next ω = a) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω (next ω) ∈ A (next ω)} =
      (Measure.infinitePi κ) E * p := by
  classical
  let μ := Measure.infinitePi κ
  let C : (Finset ι × ι) → Set (ι → α) := fun x => {ω | ω ∈ E ∧ revealed ω = x.1 ∧ next ω = x.2}
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
  let D : (Finset ι × ι) → Set (ι → α) := fun x => C x ∩ {ω | ω x.2 ∈ A x.2}
  have hDmeas (x : Finset ι × ι) : MeasurableSet (D x) :=
    (hCmeas x).inter ((hA x.2).preimage (measurable_pi_apply x.2))
  have hDdisj : Pairwise (fun x y => Disjoint (D x) (D y)) := by
    intro x y hxy
    exact (hCdisj hxy).mono Set.inter_subset_left Set.inter_subset_left
  have hDcover : (⋃ x, D x) = {ω | ω ∈ E ∧ ω (next ω) ∈ A (next ω)} := by
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
        have hh := hfresh ω hω.1
        rw [hω.2.1,hω.2.2] at hh
        exact hh ha
      simp [D, hempty]
    · by_cases he : C x = ∅
      · simp [D, he]
      · obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr he
        have hx : κ x.2 (A x.2) = p := by simpa [hω.2.2] using hsame ω hω.1
        rw [← hx]
        exact fresh_coordinate_event_general κ A hA x.1 x.2 ha (C x) (hClocal x)
  calc
    μ {ω | ω ∈ E ∧ ω (next ω) ∈ A (next ω)} = μ (⋃ x, D x) := by rw [hDcover]
    _ = ∑' x, μ (D x) := measure_iUnion hDdisj hDmeas
    _ = ∑' x, μ (C x) * p := by simp_rw [hfactor]
    _ = (∑' x, μ (C x)) * p := ENNReal.tsum_mul_right
    _ = μ (⋃ x, C x) * p := by rw [measure_iUnion hCdisj hCmeas]
    _ = μ E * p := by rw [hCcover]
