-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_chronological_prefix_independence_implies_mutual_independence_20261116
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:21:53.004227+00:00
-- url     : https://prove2.me/submissions/16c886e4-bf98-402a-b121-a59eeee7f78f

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
noncomputable section
theorem AvramDividend.Classical.avram_a27_finite_chronological_prefix_independence_implies_mutual_independence_20261116
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : ℕ → Ω → E)
    (hMeas : ∀ i < n, Measurable (Y i))
    (hPrefix : ∀ k < n,
      IndepFun (fun ω : Ω => fun i : Fin k => Y i.val ω)
        (Y k) P) :
    iIndepFun (fun i : Fin n => Y i.val) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S0 A hA
  have key : ∀ k, k ≤ n → ∀ S : Finset (Fin n), S ⊆ S0 → (∀ i ∈ S, i.val < k) →
      P (⋂ i ∈ S, (fun i : Fin n => Y i.val) i ⁻¹' A i) =
        ∏ i ∈ S, P ((fun i : Fin n => Y i.val) i ⁻¹' A i) := by
    intro k
    induction k with
    | zero =>
      intro _ S _ hS
      have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun i hi => by have := hS i hi; omega)
      subst this; simp
    | succ k ih =>
      intro hk S hsub hS
      by_cases hkS : (⟨k, by omega⟩ : Fin n) ∈ S
      · set S' := S.erase ⟨k, by omega⟩ with hS'
        have hS'lt : ∀ i ∈ S', i.val < k := by
          intro i hi
          have h1 := Finset.ne_of_mem_erase hi
          have h2 := hS i (Finset.mem_of_mem_erase hi)
          have : i.val ≠ k := fun h => h1 (Fin.ext h)
          omega
        have hSeq : S = insert ⟨k, by omega⟩ S' := (Finset.insert_erase hkS).symm
        rw [hSeq, Finset.prod_insert (Finset.notMem_erase _ _), Finset.set_biInter_insert]
        -- prefix event
        let B : Set (Fin k → E) := ⋂ i ∈ S', {x | ∀ h : i.val < k, x ⟨i.val, h⟩ ∈ A i}
        have hB : MeasurableSet B := by
          refine Finset.measurableSet_biInter _ (fun i hi => ?_)
          by_cases h : i.val < k
          · have : {x : Fin k → E | ∀ h : i.val < k, x ⟨i.val, h⟩ ∈ A i} =
                (fun x : Fin k → E => x ⟨i.val, h⟩) ⁻¹' A i := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_preimage]
              exact ⟨fun hx => hx h, fun hx _ => hx⟩
            rw [this]; exact (measurable_pi_apply _) (hA i (hsub (Finset.mem_of_mem_erase hi)))
          · have : {x : Fin k → E | ∀ h : i.val < k, x ⟨i.val, h⟩ ∈ A i} = Set.univ := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
              intro h'; exact absurd h' h
            rw [this]; exact MeasurableSet.univ
        have hpre : (⋂ i ∈ S', (fun i : Fin n => Y i.val) i ⁻¹' A i) =
            (fun ω : Ω => fun i : Fin k => Y i.val ω) ⁻¹' B := by
          ext ω
          simp only [Set.mem_iInter, Set.mem_preimage, B, Set.mem_setOf_eq]
          constructor
          · intro h i hi _; exact h i hi
          · intro h i hi; exact h i hi (hS'lt i hi)
        have hAk : MeasurableSet (A ⟨k, by omega⟩) := hA _ (hsub hkS)
        rw [Set.inter_comm, hpre, (hPrefix k (by omega)).measure_inter_preimage_eq_mul _ _ hB hAk,
          ← hpre, ih (by omega) S' ((Finset.erase_subset _ _).trans hsub) hS'lt, mul_comm]
      · exact ih (by omega) S hsub (fun i hi => by
          have h1 := hS i hi
          have : i.val ≠ k := fun h => hkS (by have e : i = ⟨k, by omega⟩ := Fin.ext h; rw [← e]; exact hi)
          omega)
  exact key n le_rfl S0 subset_rfl (fun i _ => i.isLt)

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : ℕ → Ω → E)
    (hMeas : ∀ i < n, Measurable (Y i))
    (hPrefix : ∀ k < n,
      IndepFun (fun ω : Ω => fun i : Fin k => Y i.val ω)
        (Y k) P) :
    iIndepFun (fun i : Fin n => Y i.val) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S0 A hA
  have key : ∀ k, k ≤ n → ∀ S : Finset (Fin n), S ⊆ S0 → (∀ i ∈ S, i.val < k) →
      P (⋂ i ∈ S, (fun i : Fin n => Y i.val) i ⁻¹' A i) =
        ∏ i ∈ S, P ((fun i : Fin n => Y i.val) i ⁻¹' A i) := by
    intro k
    induction k with
    | zero =>
      intro _ S _ hS
      have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun i hi => by have := hS i hi; omega)
      subst this; simp
    | succ k ih =>
      intro hk S hsub hS
      by_cases hkS : (⟨k, by omega⟩ : Fin n) ∈ S
      · set S' := S.erase ⟨k, by omega⟩ with hS'
        have hS'lt : ∀ i ∈ S', i.val < k := by
          intro i hi
          have h1 := Finset.ne_of_mem_erase hi
          have h2 := hS i (Finset.mem_of_mem_erase hi)
          have : i.val ≠ k := fun h => h1 (Fin.ext h)
          omega
        have hSeq : S = insert ⟨k, by omega⟩ S' := (Finset.insert_erase hkS).symm
        rw [hSeq, Finset.prod_insert (Finset.notMem_erase _ _), Finset.set_biInter_insert]
        -- prefix event
        let B : Set (Fin k → E) := ⋂ i ∈ S', {x | ∀ h : i.val < k, x ⟨i.val, h⟩ ∈ A i}
        have hB : MeasurableSet B := by
          refine Finset.measurableSet_biInter _ (fun i hi => ?_)
          by_cases h : i.val < k
          · have : {x : Fin k → E | ∀ h : i.val < k, x ⟨i.val, h⟩ ∈ A i} =
                (fun x : Fin k → E => x ⟨i.val, h⟩) ⁻¹' A i := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_preimage]
              exact ⟨fun hx => hx h, fun hx _ => hx⟩
            rw [this]; exact (measurable_pi_apply _) (hA i (hsub (Finset.mem_of_mem_erase hi)))
          · have : {x : Fin k → E | ∀ h : i.val < k, x ⟨i.val, h⟩ ∈ A i} = Set.univ := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
              intro h'; exact absurd h' h
            rw [this]; exact MeasurableSet.univ
        have hpre : (⋂ i ∈ S', (fun i : Fin n => Y i.val) i ⁻¹' A i) =
            (fun ω : Ω => fun i : Fin k => Y i.val ω) ⁻¹' B := by
          ext ω
          simp only [Set.mem_iInter, Set.mem_preimage, B, Set.mem_setOf_eq]
          constructor
          · intro h i hi _; exact h i hi
          · intro h i hi; exact h i hi (hS'lt i hi)
        have hAk : MeasurableSet (A ⟨k, by omega⟩) := hA _ (hsub hkS)
        rw [Set.inter_comm, hpre, (hPrefix k (by omega)).measure_inter_preimage_eq_mul _ _ hB hAk,
          ← hpre, ih (by omega) S' ((Finset.erase_subset _ _).trans hsub) hS'lt, mul_comm]
      · exact ih (by omega) S hsub (fun i hi => by
          have h1 := hS i hi
          have : i.val ≠ k := fun h => hkS (by have e : i = ⟨k, by omega⟩ := Fin.ext h; rw [← e]; exact hi)
          omega)
  exact key n le_rfl S0 subset_rfl (fun i _ => i.isLt)

