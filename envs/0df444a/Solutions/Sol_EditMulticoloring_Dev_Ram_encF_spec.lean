-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.encF_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:45.990783+00:00
-- url     : https://prove2.me/submissions/b170d840-4c2a-45ca-8b68-f0af3a0bb42c

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_greedy_length_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_shortW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le

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

/-- The digits of `T[i]` (length `ρ`) are the `i`-th table word. -/
theorem shortW_entry {q : ℕ} (hq : 0 < q) (t h r a : ℕ) (st : HS)
    (hρ : st.regs r = shortLength q t h) (hN : st.regs (r + 1) = q ^ shortLength q t h)
    (i : ℕ) (hi : i < (shortTable q t h).length) :
    Code.repr q (shortLength q t h) (((shortW q t r a).exec inp st).arr a i) = (shortTable q t h)[i] := by
  obtain ⟨h1, -, -, -, h5⟩ := shortW_table inp hq t h r a st hρ hN
  rw [h1 i hi, repr_value _ _ (h5 _ (List.getElem_mem hi))]

end Table

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncode
/-!
# The encoder program (q379, Part E), part 1: the program and its first phases

`encProg q t` (run from `HS.init n`, input `toWord u`):

* A: `paramsW` (registers `100 ..`, prime table in array `1`), `modulusW` (`p` in register `150`);
* B: read the `k` input symbols into array `2` (`readW`), copy `x = u.take m` into the input buffer
  of `colorsAll` (`copyW`), `j := value (u.drop m)` (`valueW`, register `2`);
* C: `colorsAll` (`Cx` in register `3`, `V` in register `4`, neighbour colours in array `6`);
* D: the good-index loop (`sel` in register `6`);
* E: `idx := (sel % q^h₁) * q^h₂ + (Cx % PR[sel]) % q^h₂` (register `22`);
* F: `shortW` (base register `310 + 12 t`, table array `14 + 4 t`);
* G: emit `x`, then the table word `T[idx]` (if `idx` is below the table length), flag `30 := 1`.

The short-table routines come from the namespace copy `RamEncodeS*` of `RamShort*` (the originals
clash with `RamColor` on two names).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Layout and program -/

/-! ## Invariant kept from phase A on -/

theorem ParamsAt.congr {s s' : HS} {O q t n : ℕ} (h : ParamsAt s O q t n)
    (hr : ∀ r, O ≤ r → r < O + 17 → s'.regs r = s.regs r) : ParamsAt s' O q t n := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨(hr _ (by omega) (by omega)).trans a0, (hr _ (by omega) (by omega)).trans a1,
    (hr _ (by omega) (by omega)).trans a2, (hr _ (by omega) (by omega)).trans a3,
    (hr _ (by omega) (by omega)).trans a4, (hr _ (by omega) (by omega)).trans a5,
    (hr _ (by omega) (by omega)).trans a6, (hr _ (by omega) (by omega)).trans a7,
    (hr _ (by omega) (by omega)).trans a8, (hr _ (by omega) (by omega)).trans a9,
    (hr _ (by omega) (by omega)).trans a10, (hr _ (by omega) (by omega)).trans a11,
    (hr _ (by omega) (by omega)).trans a12, (hr _ (by omega) (by omega)).trans a13,
    (hr _ (by omega) (by omega)).trans a14, (hr _ (by omega) (by omega)).trans a15,
    (hr _ (by omega) (by omega)).trans a16⟩

theorem EBase.congr {q t n p : ℕ} {s s' : HS} (h : EBase q t n p s)
    (hr : ∀ r, (r = 1 ∨ (100 ≤ r ∧ r < 117) ∨ r = 150) → s'.regs r = s.regs r)
    (ha : ∀ i, s'.arr 1 i = s.arr 1 i) : EBase q t n p s' :=
  ⟨h.par.congr (fun r h1 h2 => hr r (Or.inr (Or.inl ⟨h1, h2⟩))), (hr 1 (Or.inl rfl)).trans h.r1,
    (hr 150 (Or.inr (Or.inr rfl))).trans h.rp, fun i hi => (ha i).trans (h.pr i hi)⟩

/-- The common frame: registers below `100` other than `1`, or at least `176`, may change. -/
theorem EBase.congr' {q t n p : ℕ} {s s' : HS} (h : EBase q t n p s)
    (hr : ∀ r, 100 ≤ r → r < 176 → s'.regs r = s.regs r) (h1 : s'.regs 1 = s.regs 1)
    (ha : ∀ i, s'.arr 1 i = s.arr 1 i) : EBase q t n p s' :=
  h.congr (fun r hr' => by
    rcases hr' with rfl | hr' | rfl
    · exact h1
    · exact hr r hr'.1 (by omega)
    · exact hr _ (by omega) (by omega)) ha

/-! ## Phase A -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncode3
/-!
# The encoder program (q379, Part E), part 3: phases E, F, G

* `value_serialize`: `value (serialize q P (a, b)) = (a % q^h₁) * q^h₂ + b % q^h₂`;
* `encE_spec`: register `22` holds `value (serialize q P (sel, Cx % primeAt sel))`;
* `encF_spec`: the short table (`shortW`);
* `encG_spec`: the output.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## `value` of `serialize` -/

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encM_eq (q t n : ℕ) : encM q t n = 4 * (q ^ (parameters q t n).k + q ^ (parameters q t n).h +
    q ^ (parameters q t n).ρ + (parameters q t n).Q ^ 2 + encPW q t n + primeBound (parameters q t n).L +
    visBound q t (parameters q t n).m + (parameters q t n).h + (parameters q t n).k + (parameters q t n).L +
    (parameters q t n).K + n + q + t + 400) := rfl

/-! ## Phase E -/

/-! ## Phase F -/

theorem encF_spec_oai (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s) :
    let s' := (encF q t).exec inp s
    let T := shortTable q t (parameters q t n).h
    EBase q t n p s' ∧ (∀ r, r < 310 + 12 * t → s'.regs r = s.regs r) ∧
    (∀ y i, y < 14 + 4 * t → s'.arr y i = s.arr y i) ∧
    (∀ i (hi : i < T.length), Code.repr q (parameters q t n).ρ (s'.arr (14 + 4 * t) i) = T[i]) ∧
    (∀ i, i < T.length → s'.arr (14 + 4 * t) i < q ^ (parameters q t n).ρ) ∧
    T.length = min (q ^ (parameters q t n).h) (s'.regs (312 + 12 * t)) ∧
    (∀ z ∈ T, z.length = (parameters q t n).ρ) ∧ s'.regs (312 + 12 * t) ≤ q ^ (parameters q t n).ρ ∧
    s'.cur = s.cur ∧ s'.out = s.out ∧
    (encF q t).cost inp B s ≤ 2 * kappa B (RAM.bits (encM q t n)) +
      EncS.shortCost B q t (parameters q t n).ρ (14 + 4 * t) := by
  intro s' T
  set P := parameters q t n with hP
  have hMe := encM_eq q t n
  rw [← hP] at hMe
  have hq0 : 0 < q := by omega
  set s0 := (seqs [cp (310 + 12 * t) 113, cp (311 + 12 * t) 114]).exec inp s with hs0
  have pρ : s.regs 113 = P.ρ := hs.par.hρ
  have pqρ : s.regs 114 = q ^ P.ρ := hs.par.hqρ
  have r0 : ∀ r, r < 310 + 12 * t → s0.regs r = s.regs r := by
    intro r hr; simp [hs0, Function.update_apply, show r ≠ 310 + 12 * t by omega,
      show r ≠ 311 + 12 * t by omega]
  have e0 : s0.regs (310 + 12 * t) = shortLength q t P.h := by
    simp [hs0, Function.update_apply, pρ]; rfl
  have e1 : s0.regs (310 + 12 * t + 1) = q ^ shortLength q t P.h := by
    simp only [hs0, exec_seqs_cons, exec_seqs_nil, exec_cp, HS.setR_regs]
    rw [show 310 + 12 * t + 1 = 311 + 12 * t by omega, Function.update_self,
      Function.update_of_ne (by omega), pqρ]
    rfl
  have m0 : s0.mem = s.mem := by simp [hs0]
  have c0 : (seqs [cp (310 + 12 * t) 113, cp (311 + 12 * t) 114]).cost inp B s ≤
      2 * kappa B (RAM.bits (encM q t n)) := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_cp, exec_seqs_cons, exec_cp, HS.setR_regs]
    rw [Function.update_of_ne (by omega), pρ, pqρ]
    have := kappa_bits_le B (a := P.ρ) (M := encM q t n) (by
      have : P.ρ < q ^ P.ρ := Nat.lt_pow_self (by omega)
      omega)
    have := kappa_bits_le B (a := q ^ P.ρ) (M := encM q t n) (by omega)
    omega
  have hρe : P.ρ = shortLength q t P.h := rfl
  obtain ⟨⟨-, -, f2, -, -, -, -, -, -, fr, fa, fc, fo⟩, fcost⟩ :=
    EncS.shortW_spec inp B hq0 t (310 + 12 * t) (14 + 4 * t) P.ρ s0 e0 e1
  obtain ⟨t1, t2, -, -, t5⟩ := EncS.shortW_table inp hq0 t P.h (310 + 12 * t) (14 + 4 * t) s0 e0 e1
  have hs' : s' = (EncS.shortW q t (310 + 12 * t) (14 + 4 * t)).exec inp s0 := rfl
  rw [← hs'] at f2 fr fa fc fo t1 t2
  have hent := EncS.shortW_entry inp hq0 t P.h (310 + 12 * t) (14 + 4 * t) s0 e0 e1
  rw [← hs'] at hent
  have rr : ∀ r, r < 310 + 12 * t → s'.regs r = s.regs r := fun r hr => by
    rw [fr r (Or.inl hr), r0 r hr]
  refine ⟨hs.congr' (fun r h1 h2 => rr r (by omega)) (rr 1 (by omega)) (fun i => by
      rw [fa 1 i (Or.inl (by omega))]; simp [HS.arr, m0]), rr, ?_, hent, ?_, ?_, t5, ?_, ?_, ?_, ?_⟩
  · intro y i hy; rw [fa y i (Or.inl hy)]; simp [HS.arr, m0]
  · intro i hi
    rw [t1 i hi]
    have := EncS.value_lt T[i]
    rwa [t5 _ (List.getElem_mem hi)] at this
  · rw [t2, show 310 + 12 * t + 2 = 312 + 12 * t by omega]
  · rw [show 312 + 12 * t = 310 + 12 * t + 2 by omega, f2]
    exact EncS.greedy_length_le q t P.ρ
  · rw [fc]; simp [hs0]
  · rw [fo]; simp [hs0]
  · have hc : (encF q t).cost inp B s = (seqs [cp (310 + 12 * t) 113, cp (311 + 12 * t) 114]).cost inp B s +
        ((EncS.shortW q t (310 + 12 * t) (14 + 4 * t)).cost inp B s0 + 0) := rfl
    rw [hc]; omega

/-! ## Phase G -/

end Phases

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.encF_spec_oai := @EditMulticoloring.Dev.Ram.encF_spec_oai
