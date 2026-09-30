-- Prove2me | solution 1 for ComplementFreeCA.XOSGreedy.greedy_two_approximation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:53:53.747566+00:00
-- url     : https://prove2.me/submissions/90dc965d-0a9c-4e05-8012-1030f337c085

import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_ComplementFreeCA_XOSGreedy_GreedyRun
open Finset ComplementFreeCA.XOSGreedy

private theorem clause_le {m : ℕ} (E : XOSExpr m) (w : Fin m → ℝ) (hw : w ∈ E.clauses)
    (S : Finset (Fin m)) : ∑ j ∈ S, w j ≤ E.val S := by
  exact Finset.le_sup' (f := fun w => ∑ j ∈ S, w j) hw

private theorem demand_price_le {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl) (i : Fin n) (p : Fin m → ℝ)
    (j : Fin m) (hj : j ∈ dem i p) : p j ≤ cl i (dem i p) j := by
  have hd := hdem i p ((dem i p).erase j)
  have hv := clause_le (E i) (cl i (dem i p)) (hcl i (dem i p)).1 ((dem i p).erase j)
  have hq := (hcl i (dem i p)).2
  have hp := sum_erase_add (dem i p) p hj
  have hq' := sum_erase_add (dem i p) (cl i (dem i p)) hj
  linarith

private theorem prices_mono {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl)
    (k k' : ℕ) (hkk : k ≤ k') (j : Fin m) :
    greedyPrices dem cl k j ≤ greedyPrices dem cl k' j := by
  have hmono : Monotone (fun k => greedyPrices dem cl k j) := by
    apply monotone_nat_of_le_succ
    intro q
    change (greedyState dem cl q).prices j ≤ (greedyState dem cl (q+1)).prices j
    rw [greedyState]
    split_ifs with hq
    · simp only [greedyStep]
      split_ifs with hj
      · exact demand_price_le E dem cl hdem hcl ⟨q,hq⟩ _ j hj
      · exact le_rfl
    · exact le_rfl
  exact hmono hkk

private theorem price_increment {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hcl : IsXOSOracle E cl) (i : Fin n) :
    (∑ j, greedyPrices dem cl (i.val+1) j) - (∑ j, greedyPrices dem cl i.val j) =
      (E i).val (dem i (greedyPrices dem cl i.val)) -
        ∑ j ∈ dem i (greedyPrices dem cl i.val), greedyPrices dem cl i.val j := by
  classical
  have hp : ∀ j, greedyPrices dem cl (i.val+1) j =
      if j ∈ dem i (greedyPrices dem cl i.val) then cl i (dem i (greedyPrices dem cl i.val)) j
      else greedyPrices dem cl i.val j := by
    intro j
    simp [greedyPrices, greedyState, i.isLt, greedyStep]
    rfl
  rw [← sum_sub_distrib]
  have hfun : (fun j => greedyPrices dem cl (i.val+1) j - greedyPrices dem cl i.val j) =
      (fun j => if j ∈ dem i (greedyPrices dem cl i.val) then
        cl i (dem i (greedyPrices dem cl i.val)) j - greedyPrices dem cl i.val j else 0) := by
    funext j
    rw [hp]
    split_ifs <;> simp
  rw [hfun, ← sum_filter]
  simp only [filter_mem_eq_inter, univ_inter, sum_sub_distrib, (hcl i _).2]

private theorem opt_bound {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare E O ≤ 2 * ∑ j, greedyPrices dem cl n j := by
  classical
  let P := fun k => ∑ j, greedyPrices dem cl k j
  have hpos : ∀ k j, 0 ≤ greedyPrices dem cl k j := by
    intro k j
    simpa [greedyPrices, greedyState] using prices_mono E dem cl hdem hcl 0 k (Nat.zero_le k) j
  have hi : ∀ i : Fin n, (E i).val (O i) ≤
      P (i.val+1) - P i.val + ∑ j ∈ O i, greedyPrices dem cl n j := by
    intro i
    have hd := hdem i (greedyPrices dem cl i.val) (O i)
    have he := price_increment E dem cl hcl i
    have hle : (∑ j ∈ O i, greedyPrices dem cl i.val j) ≤ ∑ j ∈ O i, greedyPrices dem cl n j :=
      sum_le_sum (fun j hj => prices_mono E dem cl hdem hcl i.val n i.isLt.le j)
    dsimp [P]
    linarith
  have hsum := sum_le_sum (s := univ) (fun i hi' => hi i)
  have htel : (∑ i : Fin n, (P (i.val+1) - P i.val)) = P n := by
    rw [Fin.sum_univ_eq_sum_range (fun k => P (k+1)-P k) n, sum_range_sub]
    simp [P, greedyPrices, greedyState]
  rw [sum_add_distrib, htel] at hsum
  have halloc : (∑ i, ∑ j ∈ O i, greedyPrices dem cl n j) ≤ P n := by
    calc
      _ = ∑ j ∈ univ.biUnion O, greedyPrices dem cl n j :=
        (sum_biUnion (by intro i hi i' hi' hne; exact hO i i' hne)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun j hj hnot => hpos n j)
  unfold welfare
  dsimp [P] at *
  linarith

private theorem future_empty {n m : ℕ}
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (k : ℕ) : ∀ i : Fin n, k ≤ i.val → (greedyState dem cl k).bundles i = ∅ := by
  induction k with
  | zero => intro i hi; rfl
  | succ k ih =>
    intro i hi
    rw [greedyState]
    split_ifs with hk
    · have hne : i ≠ (⟨k,hk⟩:Fin n) := by
        intro he
        have := congrArg Fin.val he
        simp only at this
        omega
      have hnot : ¬ i < (⟨k,hk⟩:Fin n) := by change ¬ i.val < k; omega
      simp only [greedyStep, if_neg hne, if_neg hnot]
      exact ih i (by omega)
    · exact ih i (by omega)

private theorem state_invariant {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hcl : IsXOSOracle E cl) (k : ℕ) :
    IsAllocation (greedyState dem cl k).bundles ∧
    (∀ i, ∃ w ∈ (E i).clauses, ∀ j ∈ (greedyState dem cl k).bundles i,
      (greedyState dem cl k).prices j = w j) ∧
    (∀ j, (∀ i, j ∉ (greedyState dem cl k).bundles i) → (greedyState dem cl k).prices j = 0) := by
  classical
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro i i' hii'; simp [greedyState]
    · intro i
      obtain ⟨w,hw⟩ := (E i).nonempty
      exact ⟨w,hw,by simp [greedyState]⟩
    · intro j hj; rfl
  | succ k ih =>
    rw [greedyState]
    split_ifs with hk
    · let ki : Fin n := ⟨k,hk⟩
      let s := greedyState dem cl k
      let D := dem ki s.prices
      let ns := greedyStep dem cl ki s
      change IsAllocation ns.bundles ∧ (∀ i, ∃ w ∈ (E i).clauses, ∀ j ∈ ns.bundles i, ns.prices j = w j) ∧
        (∀ j, (∀ i, j ∉ ns.bundles i) → ns.prices j = 0)
      have hnew : ns.bundles ki = D := by simp [ns, greedyStep, D]
      have hsub : ∀ i, i ≠ ki → ns.bundles i ⊆ s.bundles i := by
        intro i hi
        change (if i = ki then D else if i < ki then s.bundles i \ D else s.bundles i) ⊆ s.bundles i
        rw [if_neg hi]
        split_ifs
        · exact sdiff_subset
        · exact subset_rfl
      have hdisj : ∀ i, i ≠ ki → Disjoint D (ns.bundles i) := by
        intro i hi
        change Disjoint D (if i = ki then D else if i < ki then s.bundles i \ D else s.bundles i)
        rw [if_neg hi]
        split_ifs with hil
        · exact disjoint_left.mpr (fun j hj hj' => (mem_sdiff.mp hj').2 hj)
        · have hi' : k ≤ i.val := by change ¬ i.val < k at hil; omega
          have he := future_empty dem cl k i hi'
          change s.bundles i = ∅ at he
          simp [he]
      refine ⟨?_, ?_, ?_⟩
      · intro i i' hne
        by_cases hi : i = ki
        · subst i
          rw [hnew]
          exact hdisj i' (Ne.symm hne)
        · by_cases hi' : i' = ki
          · subst i'
            rw [hnew]
            exact (hdisj i hi).symm
          · exact (ih.1 i i' hne).mono (hsub i hi) (hsub i' hi')
      · intro i
        by_cases hi : i = ki
        · subst i
          refine ⟨cl ki D, (hcl ki D).1, ?_⟩
          intro j hj
          rw [hnew] at hj
          simp [ns, greedyStep, D, hj]
        · obtain ⟨w,hw,he⟩ := ih.2.1 i
          refine ⟨w,hw,?_⟩
          intro j hj
          have hjD : j ∉ D := fun h => disjoint_left.mp (hdisj i hi) h hj
          change (if j ∈ D then cl ki D j else s.prices j) = w j
          rw [if_neg hjD]
          exact he j (hsub i hi hj)
      · intro j hj
        have hjD : j ∉ D := by simpa only [hnew] using hj ki
        have hnone : ∀ i, j ∉ s.bundles i := by
          intro i hmem
          by_cases hi : i = ki
          · subst i
            have he := future_empty dem cl k ki (by simp [ki])
            change s.bundles ki = ∅ at he
            simpa [he] using hmem
          · have hm : j ∈ ns.bundles i := by
              change j ∈ (if i = ki then D else if i < ki then s.bundles i \ D else s.bundles i)
              rw [if_neg hi]
              split_ifs
              · exact mem_sdiff.mpr ⟨hmem,hjD⟩
              · exact hmem
            exact hj i hm
        change (if j ∈ D then cl ki D j else s.prices j) = 0
        rw [if_neg hjD]
        exact ih.2.2 j hnone
    · exact ih

private theorem prices_le_welfare {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl) :
    ∑ j, greedyPrices dem cl n j ≤ welfare E (greedyAlloc dem cl) := by
  classical
  obtain ⟨halloc,hclause,hzero⟩ := state_invariant E dem cl hcl n
  have heq : (∑ i, ∑ j ∈ greedyAlloc dem cl i, greedyPrices dem cl n j) = ∑ j, greedyPrices dem cl n j := by
    rw [← sum_biUnion (by intro i hi i' hi' hne; exact halloc i i' hne)]
    apply sum_subset (subset_univ _)
    intro j hj hnot
    apply hzero j
    intro i hmem
    exact hnot (mem_biUnion.mpr ⟨i, mem_univ _, hmem⟩)
  rw [← heq]
  apply sum_le_sum
  intro i hi
  obtain ⟨w,hw,he⟩ := hclause i
  calc
    ∑ j ∈ greedyAlloc dem cl i, greedyPrices dem cl n j = ∑ j ∈ greedyAlloc dem cl i, w j :=
      sum_congr rfl (fun j hj => he j hj)
    _ ≤ _ := clause_le (E i) w hw _

theorem solution {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare E O ≤ 2 * welfare E (greedyAlloc dem cl) := by
  have h1 := opt_bound E dem cl hdem hcl O hO
  have h2 := prices_le_welfare E dem cl hdem hcl
  linarith
