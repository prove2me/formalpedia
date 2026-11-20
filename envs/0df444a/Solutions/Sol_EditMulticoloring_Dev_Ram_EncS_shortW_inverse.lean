-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EncS.shortW_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:29.504121+00:00
-- url     : https://prove2.me/submissions/04e0d599-18ee-4a68-84c0-eece39d2ae4e

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_shortW_spec

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

theorem mem_of_mem_greedy {q : ℕ} (t : ℕ) {xs : List (Word q)} {z : Word q}
    (h : z ∈ greedy t xs) : z ∈ xs := (greedy_sublist t xs).subset h

theorem length_of_mem_greedy_words {q : ℕ} (t l : ℕ) {z : Word q}
    (h : z ∈ greedy t (words q l)) : z.length = l :=
  length_of_mem_words l (mem_of_mem_greedy t h)

/-! ## Writing the digits of a number -/

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncodeS4
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Short table, part 4: the program `shortW` and its specification (q379, Part S)

`shortW q t r a` (static `q`, `t`; register base `r`, array base `a`), inputs `regs r = ρ`,
`regs (r + 1) = q ^ ρ`:
1. `MARK[u] := 0`, `INV[u] := 0` for `u < q^ρ` (arrays `a + 1`, `a + 2`), `cnt := 0`;
2. for `v = 0 .. q^ρ - 1`: if `MARK[v] = 0` then `T[cnt] := v` (array `a`), `INV[v] := cnt + 1`,
   `cnt += 1`, and mark every length-`ρ` word of `ball (2t) (repr q ρ v)`.

`shortW_spec`: the final state satisfies `SInv` for `greedy t (words q ρ)`, with the cost bound
`shortCost`.  `shortW_table`: the corollaries for `shortTable q t h` (`ρ = shortLength q t h`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-! ## Corollaries for `shortTable` -/

theorem idxOf_take_of_mem {α : Type*} [BEq α] [LawfulBEq α] (L : List α) (n : ℕ) {z : α}
    (h : z ∈ L.take n) : (L.take n).idxOf z = L.idxOf z := by
  conv_rhs => rw [← List.take_append_drop n L]
  rw [List.idxOf_append, if_pos h]

theorem mem_take_iff_idxOf {α : Type*} [BEq α] [LawfulBEq α] (L : List α) (n : ℕ) (z : α) :
    z ∈ L.take n ↔ z ∈ L ∧ L.idxOf z < n := by
  constructor
  · intro h
    refine ⟨List.mem_of_mem_take h, ?_⟩
    rw [← idxOf_take_of_mem L n h]
    have := List.idxOf_lt_length_of_mem h
    rw [List.length_take] at this
    omega
  · rintro ⟨h1, h2⟩
    have hl : L.idxOf z < L.length := List.idxOf_lt_length_of_mem h1
    have : (L.take n)[L.idxOf z]'(by rw [List.length_take]; omega) = z := by
      rw [List.getElem_take]; exact List.getElem_idxOf hl
    rw [← this]; exact List.getElem_mem _

section Table
variable (inp : ℕ → ℕ)

/-- **The short table read off the final state of `shortW`** (with `ρ = shortLength q t h`):
`T[i]` is the value of the `i`-th table word; the table has `min (q^h) cnt` words; a word `z` of
length `ρ` is in the table iff `INV[value z] ≠ 0 ∧ INV[value z] - 1 < q^h`, and then its index
is `INV[value z] - 1`; all table words have length `ρ`. -/
theorem shortW_table {q : ℕ} (hq : 0 < q) (t h r a : ℕ) (st : HS)
    (hρ : st.regs r = shortLength q t h) (hN : st.regs (r + 1) = q ^ shortLength q t h) :
    (∀ i (hi : i < (shortTable q t h).length),
      ((shortW q t r a).exec inp st).arr a i = value (shortTable q t h)[i]) ∧
    (shortTable q t h).length = min (q ^ h) (((shortW q t r a).exec inp st).regs (r + 2)) ∧
    (∀ z : Word q, z.length = shortLength q t h →
      (z ∈ shortTable q t h ↔ ((shortW q t r a).exec inp st).arr (a + 2) (value z) ≠ 0 ∧
        ((shortW q t r a).exec inp st).arr (a + 2) (value z) - 1 < q ^ h)) ∧
    (∀ z : Word q, z ∈ shortTable q t h →
      (shortTable q t h).idxOf z = ((shortW q t r a).exec inp st).arr (a + 2) (value z) - 1) ∧
    (∀ z : Word q, z ∈ shortTable q t h → z.length = shortLength q t h) := by
  set ρ := shortLength q t h with hρdef
  obtain ⟨⟨-, -, e2, -, -, -, hT, -, hINV, -⟩, -⟩ := shortW_spec inp 0 hq t r a ρ st hρ hN
  set G := greedy t (words q ρ) with hG
  have hTab : shortTable q t h = G.take (q ^ h) := rfl
  have hlenG : ∀ z ∈ G, z.length = ρ := fun z hz => length_of_mem_greedy_words t ρ hz
  have hINVz : ∀ z : Word q, z.length = ρ → ((shortW q t r a).exec inp st).arr (a + 2) (value z) =
      if z ∈ G then G.idxOf z + 1 else 0 := by
    intro z hz
    have := hINV (value z) (hz ▸ value_lt z)
    rwa [repr_value z ρ hz] at this
  rw [hTab]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [List.getElem_take]
    exact hT i (by rw [List.length_take] at hi; omega)
  · rw [List.length_take, e2]
  · intro z hz
    rw [mem_take_iff_idxOf, hINVz z hz]
    by_cases hzG : z ∈ G
    · simp [hzG]
    · simp [hzG]
  · intro z hz
    rw [idxOf_take_of_mem _ _ hz, hINVz z (hlenG z (List.mem_of_mem_take hz)),
      if_pos (List.mem_of_mem_take hz)]
    rfl
  · intro z hz; exact hlenG z (List.mem_of_mem_take hz)

/-- `shortInverse` read off the final state of `shortW` (`ρ = shortLength q t h`). -/
theorem shortW_inverse_oai {q : ℕ} (hq : 0 < q) (t h r a : ℕ) (st : HS)
    (hρ : st.regs r = shortLength q t h) (hN : st.regs (r + 1) = q ^ shortLength q t h)
    (z : Word q) :
    shortInverse t h z =
      if z.length = shortLength q t h ∧ ((shortW q t r a).exec inp st).arr (a + 2) (value z) ≠ 0 ∧
          ((shortW q t r a).exec inp st).arr (a + 2) (value z) - 1 < q ^ h
      then some (Code.repr q h (((shortW q t r a).exec inp st).arr (a + 2) (value z) - 1))
      else none := by
  obtain ⟨-, -, h3, h4, h5⟩ := shortW_table inp hq t h r a st hρ hN
  unfold shortInverse
  by_cases hz : z ∈ shortTable q t h
  · have hl := h5 z hz
    rw [if_pos hz, if_pos ⟨hl, (h3 z hl).mp hz⟩, h4 z hz]
  · rw [if_neg hz, if_neg]
    rintro ⟨hl, h⟩
    exact hz ((h3 z hl).mpr h)

end Table

end EditMulticoloring.Dev.Ram.EncS
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EncS.shortW_inverse_oai := @EditMulticoloring.Dev.Ram.EncS.shortW_inverse_oai
