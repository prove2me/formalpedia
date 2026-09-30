-- Prove2me | solution 1 for ComplementFreeCA.XOSGreedy.prices_nondecreasing
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:49:08.577277+00:00
-- url     : https://prove2.me/submissions/0708b04a-b3e7-4354-b06f-7507a060324f

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

theorem solution {n m : ℕ} (E : Fin n → XOSExpr m)
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
