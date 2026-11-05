-- Prove2me | solution 1 for DynAssortPers.Regret.lemma_exploration_count
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:58:33.397198+00:00
-- url     : https://prove2.me/submissions/f5c4e02c-c226-4bfc-ae58-d9b1a20c1bb5

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Algorithm2

open DynAssortPers.Regret

open scoped Classical

namespace DAPexp

lemma sampleAux_append {m n : ℕ} (C : ℝ) (r : ℕ) (xs : List (Step m n)) (x : Step m n) :
    ∀ (t : ℕ) (O : List (Obs m n)), sampleAux C r t O (xs ++ [x]) =
      if Explores C r m n (t + xs.length) (sampleAux C r t O xs)
        then sampleAux C r t O xs ++ [x.toObs] else sampleAux C r t O xs := by
  induction xs with
  | nil => intro t O; simp [sampleAux]
  | cons y ys ih =>
    intro t O
    simp only [List.cons_append, sampleAux]
    rw [ih (t + 1)]
    have : t + 1 + ys.length = t + (ys.length + 1) := by omega
    rw [this, List.length_cons]
    congr

lemma sampleAfter_succ {m n : ℕ} (C : ℝ) (r : ℕ) (l : List (Step m n)) (k : ℕ)
    (hk : k < l.length) :
    (sampleAfter C r (l.take (k + 1))).length =
      (sampleAfter C r (l.take k)).length +
        (if Explores C r m n (k + 1) (sampleAfter C r (l.take k)) then 1 else 0) := by
  have hl : (l.take k).length = k := by simp; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  unfold sampleAfter
  rw [sampleAux_append, hl, add_comm 1 k]
  split_ifs <;> simp

theorem expl {m n : ℕ} (C : ℝ) (hC : 0 ≤ C) (r : ℕ) (T : ℕ) (hT : 1 ≤ T)
    (h : Fin T → Step m n) :
    (explorationCount C r h : ℝ) ≤ C * r * ((m : ℝ) + n) * Real.log T + 1 := by
  set l := List.ofFn h with hl
  set E : ℕ → Prop := fun k => Explores C r m n (k + 1) (sampleAfter C r (l.take k)) with hE
  set c : ℝ := C * r * ((m : ℝ) + n) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcount : explorationCount C r h = ∑ i ∈ Finset.range T, if E i then 1 else 0 := by
    unfold explorationCount
    rw [Finset.card_filter]
    exact Fin.sum_univ_eq_sum_range (fun i => if E i then 1 else 0) T
  have hlen : ∀ k ≤ T, (sampleAfter C r (l.take k)).length =
      ∑ i ∈ Finset.range k, if E i then 1 else 0 := by
    intro k
    induction k with
    | zero => intro _; simp [sampleAfter, sampleAux]
    | succ k ih =>
      intro hk
      rw [sampleAfter_succ C r l k (by simp [hl]; omega), ih (by omega), Finset.sum_range_succ]
  have hinv : ∀ k ≤ T, ((sampleAfter C r (l.take k)).length : ℝ) ≤ c * Real.log k + 1 := by
    intro k
    induction k with
    | zero => intro _; simp [sampleAfter, sampleAux]
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      have hlk : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp
        · exact Real.log_le_log (by exact_mod_cast h0) (by push_cast; linarith)
      rw [sampleAfter_succ C r l k (by simp [hl]; omega)]
      split_ifs with hx
      · have hx' : ((sampleAfter C r (l.take k)).length : ℝ) ≤ c * Real.log ((k + 1 : ℕ) : ℝ) := by
          have := hx; unfold Explores at this; push_cast at this ⊢; rw [hc]; exact this
        push_cast at hx' ⊢; linarith
      · push_cast at ih hlk ⊢
        nlinarith [mul_le_mul_of_nonneg_left hlk hc0]
  have := hinv T le_rfl
  rw [hlen T le_rfl] at this
  rw [hcount]
  push_cast at this ⊢
  exact this

end DAPexp

theorem solution {m n : ℕ} (C : ℝ) (hC : 0 ≤ C) (r : ℕ) (T : ℕ) (hT : 1 ≤ T)
    (h : Fin T → Step m n) :
    (explorationCount C r h : ℝ) ≤ C * r * ((m : ℝ) + n) * Real.log T + 1 :=
  DAPexp.expl C hC r T hT h
