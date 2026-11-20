-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EncS.greedy_length_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:54.816079+00:00
-- url     : https://prove2.me/submissions/07598f55-2a5f-4047-bf90-8652e14a9be7

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
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

/-! ## Configuration -/

/-! ## Specs of the pieces -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamLib2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Word utilities on `Cmd` (q379, Part L)

Each utility is a counted loop on registers given as parameters; every spec gives the effect,
the frame (registers outside the written list, memory, cursor, output) and a cost bound of the
form `(a * N + b) * kappa B (RAM.bits M)` under a data bound `… ≤ M`.

* `eqW`     — compare two stored blocks (flag register: 1 iff equal);
* `emitW`   — emit a stored block;
* `readW`   — read `N` input symbols, storing `v - 1`;
* `readRun` — the same, also computing the length of the leading non-EOF run (`runLen`);
* `valueW`  — Horner evaluation `V := q * V + a` (`= EditMulticoloring.Code.value`);
* `digitsW` — `D[off + i] := (V / Q ^ i) % Q` for `i < K`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Utils
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ### Equality test -/

/-! ### Emitting a stored block -/

/-! ### Reading input -/

/-! ### Horner evaluation -/

theorem horner_value {q : ℕ} (w : Word q) (g : ℕ → ℕ) (hg : ∀ i (h : i < w.length), g i = (w[i]).val) :
    horner q g w.length = value w := by
  have key : ∀ k ≤ w.length, horner q g k = (w.take k).foldl (fun a b => q * a + b.val) 0 := by
    intro k hk
    induction k with
    | zero => simp [horner]
    | succ k ih =>
      have ht : w.take (k + 1) = w.take k ++ [w[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (show k < w.length by omega)]; rfl
      rw [horner, ih (by omega), ht, List.foldl_append]
      simp [hg k (by omega)]
  rw [key _ le_rfl, List.take_length]; rfl

/-! ### Digits -/

end Utils

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncodeS1
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-! Verbatim copy of `RamShort.lean` (q379, Part S) in namespace `EditMulticoloring.Dev.Ram.EncS`:
the original clashes with `RamColor` on the names `value_lt` and `visBound`, so the two chains
cannot be imported together; the encoder uses this copy. -/

/-!
# Short table, part 1: words, values, representations, greedy (q379, Part S)

* `value_cons`, `value_lt`, `value_inj` — `value` is a bijection from words of length `l`
  onto `[0, q^l)`;
* `repr_length`, `repr_getElem`, `value_repr`, `repr_value` — `Code.repr q l` is its inverse;
* `words_eq` — `words q l = (List.range (q^l)).map (Code.repr q l)`;
* `greedy` facts: sublist of the input, no duplicates, lengths;
* the RAM routine `reprW` writing the digits of a number (`repr`) into an array.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-! ## `value` -/

theorem foldl_value_init {q : ℕ} (w : Word q) (c : ℕ) :
    w.foldl (fun a b => q * a + b.val) c = c * q ^ w.length + value w := by
  induction w generalizing c with
  | nil => simp [value]
  | cons b w ih =>
    simp only [List.foldl_cons, value, List.length_cons]
    rw [ih, ih (q * 0 + b.val)]
    simp only [mul_zero, zero_add, pow_succ]
    ring

theorem value_cons {q : ℕ} (a : Fin q) (w : Word q) :
    value (a :: w) = a.val * q ^ w.length + value w := by
  show (a :: w).foldl _ 0 = _
  rw [List.foldl_cons, foldl_value_init]
  simp

theorem value_lt {q : ℕ} (w : Word q) : value w < q ^ w.length := by
  induction w with
  | nil => simp [value]
  | cons a w ih =>
    rw [value_cons, List.length_cons, pow_succ]
    have ha : a.val + 1 ≤ q := a.isLt
    have : (a.val + 1) * q ^ w.length ≤ q * q ^ w.length := Nat.mul_le_mul_right _ ha
    nlinarith

theorem value_inj {q : ℕ} : ∀ (w w' : Word q), w.length = w'.length → value w = value w' → w = w'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: w, b :: w', hl, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [value_cons, value_cons, hl] at hv
    have h1 := value_lt w
    have h2 := value_lt w'
    rw [hl] at h1
    have hP : 0 < q ^ w'.length := by omega
    have e1 : (a.val * q ^ w'.length + value w) / q ^ w'.length = a.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt h1, zero_add]
    have e2 : (b.val * q ^ w'.length + value w') / q ^ w'.length = b.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt h2, zero_add]
    have hab : a = b := Fin.ext (by rw [← e1, ← e2, hv])
    subst hab
    have : value w = value w' := by omega
    rw [value_inj w w' hl this]

/-! ## `repr` -/

theorem repr_eq_map {q : ℕ} (hq : 0 < q) (l N : ℕ) :
    Code.repr q l N = (List.range l).map (fun i => (⟨(N / q ^ (l - 1 - i)) % q, Nat.mod_lt _ hq⟩ : Fin q)) := by
  unfold Code.repr
  rw [← List.filterMap_eq_map]
  apply List.filterMap_congr
  intro i _
  simp [Nat.mod_lt _ hq]

theorem repr_length {q : ℕ} (hq : 0 < q) (l N : ℕ) : (Code.repr q l N).length = l := by
  rw [repr_eq_map hq]; simp

theorem repr_getElem {q : ℕ} (hq : 0 < q) (l N i : ℕ) (hi : i < (Code.repr q l N).length) :
    ((Code.repr q l N)[i]).val = (N / q ^ (l - 1 - i)) % q := by
  simp only [repr_eq_map hq, List.getElem_map, List.getElem_range]

/-- The digit Horner identity: `horner` of the first `k` digits is `N / q^(l-k)`. -/
theorem horner_digits (q l N : ℕ) (hN : N < q ^ l) :
    ∀ k ≤ l, horner q (fun i => (N / q ^ (l - 1 - i)) % q) k = N / q ^ (l - k) := by
  intro k hk
  induction k with
  | zero =>
    simp only [horner, Nat.sub_zero]
    exact (Nat.div_eq_of_lt hN).symm
  | succ k ih =>
    simp only [horner]
    rw [ih (by omega)]
    have e : l - k = (l - 1 - k) + 1 := by omega
    have e2 : l - (k + 1) = l - 1 - k := by omega
    rw [e, e2, pow_succ, ← Nat.div_div_eq_div_mul]
    exact Nat.div_add_mod _ _

theorem value_repr {q : ℕ} (hq : 0 < q) (l N : ℕ) (hN : N < q ^ l) : value (Code.repr q l N) = N := by
  rw [← horner_value (Code.repr q l N) (fun i => (N / q ^ (l - 1 - i)) % q)
    (fun i h => (repr_getElem hq l N i h).symm), repr_length hq, horner_digits q l N hN l le_rfl]
  simp

theorem repr_value {q : ℕ} (w : Word q) (l : ℕ) (hl : w.length = l) : Code.repr q l (value w) = w := by
  rcases Nat.eq_zero_or_pos q with h | hq
  · subst h
    cases w with
    | nil => subst hl; rfl
    | cons a _ => exact a.elim0
  · exact value_inj _ _ (by rw [repr_length hq, hl]) (value_repr hq l _ (hl ▸ value_lt w))

/-! ## `words` -/

theorem length_of_mem_words {q : ℕ} : ∀ (l : ℕ) {w : Word q}, w ∈ words q l → w.length = l
  | 0, w, h => by simp [words] at h; subst h; rfl
  | l + 1, w, h => by
    simp only [words, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at h
    obtain ⟨a, u, hu, rfl⟩ := h
    simp [length_of_mem_words l hu]

theorem range_mul_flatMap (q m : ℕ) :
    (List.range q).flatMap (fun a => (List.range m).map (fun v => a * m + v)) = List.range (q * m) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.flatMap_append, ih, show (q + 1) * m = q * m + m by ring,
      List.range_add]
    simp

theorem words_map_value (q : ℕ) : ∀ l : ℕ, (words q l).map value = List.range (q ^ l)
  | 0 => by simp [words, value]
  | l + 1 => by
    simp only [words, List.map_flatMap, List.map_map]
    have e : ∀ a : Fin q, (words q l).map (value ∘ (a :: ·)) =
        (List.range (q ^ l)).map (fun v => a.val * q ^ l + v) := by
      intro a
      rw [← words_map_value q l, List.map_map]
      apply List.map_congr_left
      intro w hw
      simp [value_cons, length_of_mem_words l hw]
    rw [List.flatMap_congr (fun a _ => e a), finRange_flatMap, pow_succ, mul_comm (q ^ l) q,
      ← range_mul_flatMap]
    apply List.flatMap_congr
    intro a ha
    have ha' : a < q := List.mem_range.mp ha
    simp [finFlat, ha']

/-- The words of length `l`, in order, are the representations of `0, …, q^l - 1`. -/
theorem words_eq (q l : ℕ) : words q l = (List.range (q ^ l)).map (Code.repr q l) := by
  rw [← words_map_value q l, List.map_map]
  conv_lhs => rw [← List.map_id (words q l)]
  apply List.map_congr_left
  intro w hw
  simp [repr_value w l (length_of_mem_words l hw)]

theorem words_length (q l : ℕ) : (words q l).length = q ^ l := by
  rw [words_eq]; simp

/-! ## `greedy` -/

theorem greedy_eq_foldl {q : ℕ} (t : ℕ) (xs : List (Word q)) :
    greedy t xs = xs.foldl (greedyStep t) [] := rfl

theorem foldl_greedyStep_sublist {q : ℕ} (t : ℕ) (xs : List (Word q)) :
    ∀ acc : List (Word q), ∃ l, l.Sublist xs ∧ xs.foldl (greedyStep t) acc = acc ++ l := by
  induction xs with
  | nil => intro acc; exact ⟨[], List.Sublist.slnil, by simp⟩
  | cons x xs ih =>
    intro acc
    rw [List.foldl_cons]
    by_cases h : acc.any (fun z => decide (x ∈ ball (2 * t) z))
    · rw [show greedyStep t acc x = acc by simp [greedyStep, h]]
      obtain ⟨l, hl, he⟩ := ih acc
      exact ⟨l, hl.cons x, he⟩
    · rw [show greedyStep t acc x = acc ++ [x] by simp only [greedyStep, h]; simp]
      obtain ⟨l, hl, he⟩ := ih (acc ++ [x])
      exact ⟨x :: l, hl.cons_cons x, by rw [he]; simp⟩

theorem greedy_sublist {q : ℕ} (t : ℕ) (xs : List (Word q)) : (greedy t xs).Sublist xs := by
  obtain ⟨l, hl, he⟩ := foldl_greedyStep_sublist t xs []
  rw [greedy_eq_foldl, he]; simpa using hl

theorem greedy_length_le_oai (q t l : ℕ) : (greedy t (words q l)).length ≤ q ^ l := by
  rw [← words_length q l]; exact (greedy_sublist t _).length_le

/-! ## Writing the digits of a number -/

end EditMulticoloring.Dev.Ram.EncS
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EncS.greedy_length_le_oai := @EditMulticoloring.Dev.Ram.EncS.greedy_length_le_oai
