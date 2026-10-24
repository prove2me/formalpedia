-- Prove2me | solution 1 for CommitteeVoting.ExpConv.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:47:24.402552+00:00
-- url     : https://prove2.me/submissions/e1a138e5-fa95-4dcf-8df4-c76b437dfd23

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee
import Definitions.Def_CommitteeVoting_ExpConv_VoteProb

open MeasureTheory ProbabilityTheory CommitteeVoting.ExpConv

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (ballot : Fin n → Ω → Fin m → Bool) (hmeas : ∀ i, Measurable (ballot i))
    (hind : iIndepFun ballot P) (j : Fin m) (x : ℕ) :
    P.real {ω | score (fun i => ballot i ω) j = x}
      = ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x,
          (∏ i ∈ A, voteProb P ballot i j) * ∏ i ∈ Finset.univ \ A, (1 - voteProb P ballot i j) := by
  classical
  -- the approver set
  set E : Finset (Fin n) → Set Ω := fun A =>
    {ω | (Finset.univ.filter fun i => ballot i ω j = true) = A} with hE
  set S : Fin n → Finset (Fin n) → Set (Fin m → Bool) := fun i A =>
    {b | b j = decide (i ∈ A)} with hS
  have hSm : ∀ i A, MeasurableSet (S i A) := by
    intro i A
    exact measurableSet_eq_fun (measurable_pi_apply j) measurable_const
  have hEeq : ∀ A, E A = ⋂ i ∈ (Finset.univ : Finset (Fin n)), ballot i ⁻¹' S i A := by
    intro A
    ext ω
    simp only [hE, hS, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_univ,
      forall_const]
    constructor
    · intro h i
      rw [← h]
      simp
    · intro h
      ext i
      have := h i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases hb : ballot i ω j <;> simp_all
  have hEm : ∀ A, MeasurableSet (E A) := by
    intro A
    rw [hEeq]
    exact Finset.measurableSet_biInter _ (fun i _ => hmeas i (hSm i A))
  have hunion : {ω | score (fun i => ballot i ω) j = x} =
      ⋃ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x, E A := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, hE, score,
      exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨Finset.subset_univ _, h⟩, rfl⟩
    · rintro ⟨A, ⟨_, hA⟩, rfl⟩
      exact hA
  have hdisj : Set.PairwiseDisjoint (↑((Finset.univ : Finset (Fin n)).powersetCard x)) E := by
    intro A _ B _ hAB
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [hE, Set.mem_setOf_eq] at h1 h2
    exact hAB (h1.symm.trans h2)
  rw [hunion, measureReal_biUnion_finset hdisj (fun A _ => hEm A)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  have hprod := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind) Finset.univ
    (sets := fun i => S i A) (fun i _ => hSm i A)
  have hpt : ∀ i, P.real (ballot i ⁻¹' S i A) =
      if i ∈ A then voteProb P ballot i j else 1 - voteProb P ballot i j := by
    intro i
    have hT : MeasurableSet {ω | ballot i ω j = true} :=
      measurableSet_eq_fun ((measurable_pi_apply j).comp (hmeas i)) measurable_const
    split_ifs with hi
    · simp only [voteProb, hS, hi, decide_true]
      rfl
    · have : ballot i ⁻¹' S i A = {ω | ballot i ω j = true}ᶜ := by
        ext ω; simp [hS, hi]
      rw [this, probReal_compl_eq_one_sub hT]
      rfl
  calc P.real (E A) = ∏ i, P.real (ballot i ⁻¹' S i A) := by
        rw [hEeq, measureReal_def, hprod, ENNReal.toReal_prod]
        rfl
    _ = ∏ i, (if i ∈ A then voteProb P ballot i j else 1 - voteProb P ballot i j) := by
        simp_rw [hpt]
    _ = _ := by
        rw [Finset.prod_ite]
        congr 1
        · congr 1; ext i; simp
        · congr 1; ext i; simp
