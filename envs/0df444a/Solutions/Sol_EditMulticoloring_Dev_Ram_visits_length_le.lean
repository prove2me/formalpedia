-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.visits_length_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:58.03972+00:00
-- url     : https://prove2.me/submissions/3a9fd8d8-1073-4e14-8b83-501c49e9172b

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section
-- module Solutions.EditMulticoloring.RamEnum
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator (q379, Part L)

`enumScripts q s cfg body` runs `body` once per element of `visits s x` (in list order), each
time with the visited word in array `cfg.vis` (offset 0) and its length in register `cfg.VL`.
Main theorem: `enumScripts_spec` (RamEnum3.lean); level induction in RamEnum2.lean.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The visit list -/

theorem insW_length {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) (hi : i ≤ x.length) :
    (insW x i a).length = x.length + 1 := by
  simp [insW]; omega
theorem delW_length {q : ℕ} (x : Word q) (i : ℕ) (hi : i < x.length) :
    (delW x i).length = x.length - 1 := by
  simp [delW]; omega
theorem repW_length {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) (hi : i < x.length) :
    (repW x i a).length = x.length := by
  simp [repW]; omega

theorem finRange_flatMap {q : ℕ} {β : Type*} (F : Fin q → List β) :
    (List.finRange q).flatMap F = (List.range q).flatMap (finFlat F) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_map]
    rw [ih (fun a => F a.castSucc)]
    congr 1
    · apply List.flatMap_congr
      intro a ha
      have ha' : a < n := List.mem_range.mp ha
      simp [finFlat, ha', Nat.lt_succ_of_lt ha']
    · simp [finFlat, Fin.last]

theorem flatMap_filter_eq {α β : Type*} (l : List α) (p : α → Bool) (F : α → List β) :
    (l.filter p).flatMap F = l.flatMap (fun a => if p a then F a else []) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem visits_zero {q : ℕ} (x : Word q) : visits 0 x = [x] := by
  simp [visits, scripts]

theorem visits_succ {q : ℕ} (s : ℕ) (x : Word q) :
    visits (s + 1) x = x ::
      ((List.range (x.length + 1)).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun a => visits s (insW x i a))) ++
        (List.range x.length).flatMap (fun i => visits s (delW x i)) ++
        (List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun a =>
            if x[i]? = some a then [] else visits s (repW x i a)))) := by
  simp only [visits, scripts, List.map_cons, availableEdits, List.flatMap_append, List.map_append,
    List.map_flatMap]
  congr 1
  congr 1
  congr 1
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro i hi
    have hi' : i ≤ x.length := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    rw [List.flatMap_map, ← finRange_flatMap]
    apply List.flatMap_congr
    intro a _
    simp [applyEdit, hi', insW, List.map_map]
  · rw [List.flatMap_map]
    apply List.flatMap_congr
    intro i hi
    have hi' : i < x.length := List.mem_range.mp hi
    simp [applyEdit, hi', delW, List.map_map]
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro i hi
    have hi' : i < x.length := List.mem_range.mp hi
    rw [List.flatMap_map, flatMap_filter_eq, ← finRange_flatMap]
    apply List.flatMap_congr
    intro a _
    by_cases ha : x[i]? = some a
    · simp [ha]
    · have ha2 : ¬ x[i] = a := fun h => ha (by rw [List.getElem?_eq_getElem hi', h])
      simp [applyEdit, hi', ha, ha2, repW, List.map_map]

/-! ## Configuration -/

/-! ## Specs of the pieces -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum3
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator: main theorem, size bound, toy clients (q379, Part L)

* `enumScripts_spec` — the fold specification of `enumScripts q s cfg body`;
* `visits_length_le` — `(visits s x).length ≤ ∑ i ∈ range (s+1), (2q(|x|+s+1))^i`;
* toy clients `countProg` (count the visited words of length `|x|` other than `x`) and
  `listProg` (store them as a 2-D array, word `j` at offsets `j * S`), both proved.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Size of the visit list -/

theorem flatMap_range_length_le {β : Type*} (G : ℕ → List β) (n V : ℕ)
    (h : ∀ b < n, (G b).length ≤ V) : ((List.range n).flatMap G).length ≤ n * V := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have := ih (fun b hb => h b (by omega))
    have := h n (by omega)
    rw [Nat.succ_mul]; omega

theorem flatMap_range_length_le_skip {β : Type*} (G : ℕ → List β) (n V c : ℕ) (hc : c < n)
    (h : ∀ b < n, (G b).length ≤ V) (h0 : G c = []) :
    ((List.range n).flatMap G).length ≤ (n - 1) * V := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · have := ih hc (fun b hb => h b (by omega))
      have := h n (by omega)
      have e : n + 1 - 1 = (n - 1) + 1 := by omega
      rw [e, Nat.succ_mul]; omega
    · have := flatMap_range_length_le G c V (fun b hb => h b (by omega))
      rw [h0, List.length_nil, Nat.add_zero, Nat.add_sub_cancel]; exact this

theorem visits_length_le_oai {q : ℕ} (k : ℕ) (x : Word q) :
    (visits k x).length ≤ ∑ i ∈ Finset.range (k + 1), (2 * q * (x.length + k + 1)) ^ i := by
  induction k generalizing x with
  | zero => simp [visits_zero]
  | succ k ih =>
    set T := 2 * q * (x.length + (k + 1) + 1) with hT
    set V := ∑ i ∈ Finset.range (k + 1), T ^ i with hV
    have hchild : ∀ z : Word q, z.length ≤ x.length + 1 → (visits k z).length ≤ V := by
      intro z hz
      refine (ih z).trans (Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left ?_ i)
      apply Nat.mul_le_mul_left; omega
    rw [visits_succ]
    simp only [List.length_cons, List.length_append]
    have hA := flatMap_range_length_le (fun i =>
        (List.range q).flatMap (finFlat fun b => visits k (insW x i b))) (x.length + 1) (q * V)
      (fun i hi => flatMap_range_length_le (finFlat fun b => visits k (insW x i b)) q V
        (fun b hb => by
        simp only [finFlat, hb, dif_pos]
        exact hchild _ (by rw [insW_length _ _ _ (by omega)])))
    have hD := flatMap_range_length_le (fun i => visits k (delW x i)) x.length V
      (fun i hi => hchild _ (by
      rw [delW_length _ _ hi]; omega))
    have hR := flatMap_range_length_le (fun i => (List.range q).flatMap (finFlat fun b =>
        if x[i]? = some b then [] else visits k (repW x i b))) x.length ((q - 1) * V) (fun i hi => by
      apply flatMap_range_length_le_skip (finFlat fun b =>
        if x[i]? = some b then [] else visits k (repW x i b)) q V (x[i]).val (x[i]).isLt
      · intro b hb
        simp only [finFlat, hb, dif_pos]
        split_ifs
        · simp
        · exact hchild _ (by rw [repW_length _ _ _ hi]; omega)
      · simp [finFlat, (x[i]).isLt, List.getElem?_eq_getElem hi])
    have hsum : ∑ i ∈ Finset.range (k + 1 + 1), T ^ i = 1 + T * V := by
      rw [Finset.sum_range_succ', hV, Finset.mul_sum]
      simp only [pow_zero, pow_succ]
      rw [add_comm]; congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsum]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · have hx0 : x.length = 0 := by
        cases x with
        | nil => rfl
        | cons a _ => exact (Fin.elim0 (hq ▸ a))
      have : (List.range x.length).flatMap (fun i => visits k (delW x i)) = [] := by
        rw [hx0]; rfl
      rw [this]
      have h1 : q * V = 0 := by rw [hq, zero_mul]
      have h2 : (q - 1) * V = 0 := by rw [hq]; simp
      rw [h1, mul_zero] at hA
      rw [h2, mul_zero] at hR
      simp only [List.length_nil, add_zero]
      have : 1 ≤ 1 + T * V := by omega
      omega
    · have h1 : (x.length + 1) * (q * V) + x.length * V + x.length * ((q - 1) * V) ≤ T * V := by
        have e : x.length * V + x.length * ((q - 1) * V) = x.length * (q * V) := by
          rw [← mul_add]; congr 1
          have : q = (q - 1) + 1 := by omega
          conv_rhs => rw [this]
          ring
        calc _ = (x.length + 1) * (q * V) + x.length * (q * V) := by rw [add_assoc, e]
          _ = ((2 * x.length + 1) * q) * V := by ring
          _ ≤ T * V := by
            apply Nat.mul_le_mul_right
            rw [hT]; nlinarith
      omega

/-! ## Toy client (a): counting -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.visits_length_le_oai := @EditMulticoloring.Dev.Ram.visits_length_le_oai
