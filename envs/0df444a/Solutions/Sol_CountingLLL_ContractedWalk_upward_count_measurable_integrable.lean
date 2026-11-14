-- Prove2me | solution 1 for CountingLLL.ContractedWalk.upward_count_measurable_integrable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:40:25.49498+00:00
-- url     : https://prove2.me/submissions/e8b72988-12dd-4dcf-b154-02d27c857535

import Definitions.Def_CountingLLL_ContractedGF

set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped BigOperators ENNReal

private theorem level_ext (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : level ω i t = level ω' i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ k < t, ω k = ω' k := by intro k hk; exact h k (by omega)
    have hnow := h t (by omega)
    simp only [level, ih hprev, hnow]

private theorem prefix_meas (t : ℕ) (P : Tape → Prop)
    (hP : ∀ ω ω', (∀ k < t, ω k = ω' k) → (P ω ↔ P ω')) : MeasurableSet {ω | P ω} := by
  classical
  let f : Tape → (Fin t → Bool) := fun ω j => ω j
  have hf : Measurable f := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (Fin t → Bool) := {x | ∃ ω : Tape, f ω = x ∧ P ω}
  have heq : f ⁻¹' F = {ω : Tape | P ω} := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      have he : ∀ k < t, ω k = ω' k := by intro k hk; exact (congrFun heq ⟨k,hk⟩).symm
      exact (hP ω ω' he).2 hn
    · intro hn; exact ⟨ω, rfl, hn⟩
  rw [← heq]
  exact MeasurableSet.of_discrete.preimage hf

private def countAt (ω : Tape) (i t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range t, if level ω i k ≠ 0 ∧ ω k = true then 1 else 0

private theorem count_ext (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : countAt ω i t = countAt ω' i t := by
  unfold countAt
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have he : ∀ j < k, ω j = ω' j := by intro j hj; exact h j (by omega)
  rw [level_ext ω ω' i k he, h k hk']

private theorem finite_event (i t : ℕ) (P : ℕ → ℕ → Prop) :
    MeasurableSet {ω : Tape | P (level ω i t) (countAt ω i t)} := by
  apply prefix_meas t
  intro ω ω' h
  rw [level_ext ω ω' i t h, count_ext ω ω' i t h]

private theorem stop_meas (i : ℕ) : MeasurableSet {ω : Tape | ∃ t, level ω i t = 0} := by
  have heq : {ω : Tape | ∃ t, level ω i t = 0} = ⋃ t : ℕ, {ω : Tape | level ω i t = 0} := by ext ω; simp
  rw [heq]
  exact MeasurableSet.iUnion fun t => finite_event i t (fun level _ => level = 0)

private theorem count_levelset (i n : ℕ) : MeasurableSet {ω : Tape | upwardCount ω i = n} := by
  classical
  let stop : Set Tape := {ω | ∃ t, level ω i t = 0}
  let events : ℕ → Set Tape := fun t => {ω |
    level ω i t = 0 ∧ (∀ j < t, level ω i j ≠ 0) ∧ countAt ω i t = n}
  have hev : ∀ t, MeasurableSet (events t) := by
    intro t
    have h1 := finite_event i t (fun level count => level = 0 ∧ count = n)
    have h2 : MeasurableSet (⋂ j : Fin t, {ω : Tape | level ω i j.val ≠ 0}) :=
      MeasurableSet.iInter fun j => finite_event i j.val (fun level _ => level ≠ 0)
    have heq : events t = {ω : Tape | level ω i t = 0 ∧ countAt ω i t = n} ∩
      (⋂ j : Fin t, {ω : Tape | level ω i j.val ≠ 0}) := by
      ext ω
      simp only [events, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h, hmin, hA⟩; exact ⟨⟨h,hA⟩, fun j => hmin j.val j.isLt⟩
      · rintro ⟨⟨h,hA⟩, hmin⟩; exact ⟨h, fun j hj => hmin ⟨j,hj⟩, hA⟩
    rw [heq]
    exact h1.inter h2
  have heq : {ω : Tape | upwardCount ω i = n} =
      (stopᶜ ∩ (if n=0 then Set.univ else ∅)) ∪ ⋃ t, events t := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion, events]
    constructor
    · intro hA
      by_cases h : ∃ t, level ω i t = 0
      · right
        refine ⟨Nat.find h, Nat.find_spec h, ?_, ?_⟩
        · intro j hj; exact Nat.find_min h hj
        · simpa [upwardCount, stopTime, h, countAt] using hA
      · left
        have hn : n=0 := by simpa [upwardCount, stopTime, h, countAt] using hA.symm
        simp [stop,h,hn]
    · rintro (⟨h, hA⟩ | ⟨t, ht, hmin, hA⟩)
      · change ¬ (∃ t, level ω i t = 0) at h
        have hn : n=0 := by by_contra hn; simp [hn] at hA
        subst n
        simpa [upwardCount, stopTime, h, countAt]
      · have h : ∃ t, level ω i t = 0 := ⟨t,ht⟩
        have hfind : Nat.find h = t := (Nat.find_eq_iff h).mpr ⟨ht, hmin⟩
        simpa [upwardCount, stopTime, h, hfind, countAt] using hA
  rw [heq]
  exact (stop_meas i).compl.inter (by by_cases h : n=0 <;> simp [h]) |>.union (MeasurableSet.iUnion hev)

private theorem upwardCount_measurable (i : ℕ) : Measurable (fun ω : Tape => upwardCount ω i) := by
  classical
  intro S hS
  have heq : (fun ω : Tape => upwardCount ω i) ⁻¹' S = ⋃ n : ℕ, if n ∈ S then {ω : Tape | upwardCount ω i = n} else ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro h; exact ⟨upwardCount ω i, by simp [h]⟩
    · rintro ⟨n, hn⟩
      by_cases h : n ∈ S
      · simp only [if_pos h, Set.mem_setOf_eq] at hn
        simpa [hn] using h
      · simp [h] at hn
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  by_cases h : n ∈ S
  · simpa only [if_pos h] using count_levelset i n
  · simp [h]

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

private theorem upwardCount_integrable (θ z : ℝ) (hθ : θ ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (i : ℕ) :
    Integrable (fun ω : Tape => z ^ upwardCount ω i) (tapeLaw (ENNReal.ofReal θ)) := by
  have hp : ENNReal.ofReal θ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hθ
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability' _ hp
  letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
  have hm : Measurable (fun ω : Tape => z ^ upwardCount ω i) := (upwardCount_measurable i).const_pow z
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz0 _)]
  exact pow_le_one₀ hz0 hz1


theorem solution : (∀ i : ℕ, Measurable (fun ω : Tape => upwardCount ω i)) ∧ (∀ (θ z : ℝ), θ ≤ 1 → 0 ≤ z → z ≤ 1 → ∀ i : ℕ, Integrable (fun ω : Tape => z ^ upwardCount ω i) (tapeLaw (ENNReal.ofReal θ))) := by
  exact ⟨upwardCount_measurable, upwardCount_integrable⟩
