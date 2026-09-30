-- Prove2me | solution 1 for ComplementFreeCA.XOSGreedy.optimal_welfare_le_two_final_prices
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:52:04.1423+00:00
-- url     : https://prove2.me/submissions/c9d09078-41ee-4f05-84dd-0b9c332f752a

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

theorem solution {n m : ℕ} (E : Fin n → XOSExpr m)
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
