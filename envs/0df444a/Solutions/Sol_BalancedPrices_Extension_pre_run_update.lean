-- Prove2me | solution 1 for BalancedPrices.Extension.pre_run_update
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:08.181818+00:00
-- url     : https://prove2.me/submissions/7bf4bb82-c80f-434c-b7e1-2eb1c84ca40f

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

-- carved verbatim out of submission a6966675-078f-41ef-897b-6c455a701cff, lines 39-48

section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open BalancedPrices.Extension

lemma run_eq {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (choice : ∀ i, V i → Outcome X → X i) (v : ∀ i, V i) (i : Fin n) :
    run nul choice v i = choice i (v i) (pre nul (run nul choice v) i) := by
  rw [run]
  congr 1
  funext j
  simp [pre, restrictTo]

lemma run_congr {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (choice : ∀ i, V i → Outcome X → X i) (v v' : ∀ i, V i) :
    ∀ (m : ℕ) (i : Fin n), i.val = m → (∀ k : Fin n, k ≤ i → v k = v' k) →
      run nul choice v i = run nul choice v' i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi h
    rw [run_eq, run_eq, h i le_rfl]
    congr 1
    funext j
    simp only [pre, restrictTo, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hj
    · exact ih j.val (by have := Fin.lt_def.mp hj; omega) j rfl
        (fun k hk => h k (le_trans hk hj.le))
    · rfl

theorem solution {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (choice : ∀ i, V i → Outcome X → X i) (v : ∀ i, V i) (i : Fin n) (a : V i) :
    pre nul (run nul choice (Function.update v i a)) i = pre nul (run nul choice v) i := by
  funext j
  simp only [pre, restrictTo, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with hj
  · exact run_congr nul choice _ _ j.val j rfl (fun k hk => by
      rw [Function.update_of_ne (ne_of_lt (lt_of_le_of_lt hk hj))])
  · rfl

end
