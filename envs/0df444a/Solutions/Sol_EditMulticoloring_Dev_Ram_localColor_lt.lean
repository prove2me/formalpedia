-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.localColor_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:56.77487+00:00
-- url     : https://prove2.me/submissions/6ced33e8-d821-435a-97b3-b0d08d314f84

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section
-- module Solutions.EditMulticoloring.RamGF
/-!
# GF(2)[X] arithmetic on `Cmd` (q379, Part G)

* fold forms of `binaryMul` / `binaryRem` with an arbitrary (large enough) loop count;
* value bounds (`binaryMul_lt`, `binaryRem_lt`, `fieldMul_lt`);
* `gfMul`, `gfRem`, `gfField` (= `fieldMul`) on a register block, `gfSetup` (the context).

Field-context block `g .. g+15`: `p lp P2 W N2 PN X Y Z` then scratch `g+9 .. g+15`, where
`lp = log2 p`, `P2 = 2^lp`, `N2 = 2W`, `PN = 2^(2W)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Arithmetic facts -/

theorem foldl_range_rev_stable (g : ℕ → ℕ → ℕ) (a n : ℕ) (h : ∀ i, n ≤ i → g a i = a) :
    ∀ m, n ≤ m → (List.range m).reverse.foldl g a = (List.range n).reverse.foldl g a := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show n + (d + 1) = (n + d) + 1 by omega, List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.foldl_cons]
    rw [h _ (by omega), ih (by omega)]

theorem lt_two_pow_min {b N : ℕ} (hb : b < 2 ^ N) : b < 2 ^ (min N (b.log2 + 1)) := by
  rcases le_total N (b.log2 + 1) with h | h
  · rw [min_eq_left h]; exact hb
  · rw [min_eq_right h]; exact Nat.lt_log2_self

theorem testBit_false_of_lt_pow {b n i : ℕ} (hb : b < 2 ^ n) (hi : n ≤ i) : b.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))

theorem binaryRem_fold_rev (p a N : ℕ) (ha : a < 2 ^ N) :
    binaryRem p a = (List.range N).reverse.foldl (remStep p) a := by
  have hn := lt_two_pow_min ha
  have hst : ∀ i, min N (a.log2 + 1) ≤ i → remStep p a i = a := by
    intro i hi; simp [remStep, testBit_false_of_lt_pow hn hi]
  have e1 := foldl_range_rev_stable (remStep p) a _ hst N (min_le_left _ _)
  have e2 := foldl_range_rev_stable (remStep p) a _ hst (a.log2 + 1) (min_le_right _ _)
  rw [e1, ← e2]; rfl

theorem range_reverse_eq_map (N : ℕ) :
    (List.range N).reverse = (List.range N).map (fun k => N - 1 - k) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_range, List.getElem_map, List.length_range]

/-- `binaryRem` as an upward loop over `k < N` processing bit `N - 1 - k`. -/
theorem binaryRem_fold (p a N : ℕ) (ha : a < 2 ^ N) :
    binaryRem p a = (List.range N).foldl (fun z k => remStep p z (N - 1 - k)) a := by
  rw [binaryRem_fold_rev p a N ha, range_reverse_eq_map, List.foldl_map]

theorem lt_pow_of_testBit_false {z i : ℕ} (hz : z < 2 ^ (i + 1)) (hb : z.testBit i = false) :
    z < 2 ^ i := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rcases Nat.eq_or_lt_of_le hj with rfl | hj
  · exact hb
  · exact testBit_false_of_lt_pow hz hj

theorem p_lt_pow (p : ℕ) : p < 2 ^ (p.log2 + 1) := Nat.lt_log2_self

theorem remStep_bound (p z i : ℕ) (hp : p ≠ 0) (hz : z < 2 ^ (max (i + 1) p.log2)) :
    remStep p z i < 2 ^ (max i p.log2) := by
  unfold remStep
  by_cases hi : p.log2 ≤ i
  · have hm1 : max (i + 1) p.log2 = i + 1 := by omega
    have hm2 : max i p.log2 = i := by omega
    rw [hm1] at hz; rw [hm2]
    have hpi : p * 2 ^ (i - p.log2) < 2 ^ (i + 1) := by
      calc p * 2 ^ (i - p.log2) < 2 ^ (p.log2 + 1) * 2 ^ (i - p.log2) :=
            Nat.mul_lt_mul_of_pos_right (p_lt_pow p) (by positivity)
        _ = 2 ^ (i + 1) := by rw [← pow_add]; congr 1; omega
    by_cases hb : z.testBit i = true
    · rw [if_pos ⟨hp, hi, hb⟩]
      apply lt_pow_of_testBit_false (Nat.xor_lt_two_pow hz hpi)
      have : (Nat.xor z (p * 2 ^ (i - p.log2))).testBit i = false := by
        show (z ^^^ (p * 2 ^ (i - p.log2))).testBit i = false
        rw [Nat.testBit_xor, Nat.testBit_mul_two_pow, hb]
        simp only [show i - (i - p.log2) = p.log2 by omega, Nat.testBit_log2 hp]
        simp
      exact this
    · rw [if_neg (fun h => hb h.2.2)]
      exact lt_pow_of_testBit_false hz (by simpa using hb)
  · rw [if_neg (fun h => hi h.2.1)]
    have hm1 : max (i + 1) p.log2 = p.log2 := by omega
    have hm2 : max i p.log2 = p.log2 := by omega
    rw [hm1] at hz; rw [hm2]; exact hz

theorem binaryRem_lt (p a : ℕ) (hp : p ≠ 0) : binaryRem p a < 2 ^ p.log2 := by
  set n := a.log2 + 1
  have key : ∀ k ≤ n, (List.range k).foldl (fun z k => remStep p z (n - 1 - k)) a <
      2 ^ (max (n - k) p.log2) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, Nat.sub_zero]
      exact lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have := remStep_bound p _ (n - 1 - k) hp (by
        have e : n - 1 - k + 1 = n - k := by omega
        rw [e]; exact ih (by omega))
      rw [show n - (k + 1) = n - 1 - k by omega]; exact this
  have h := key n le_rfl
  rw [Nat.sub_self, Nat.zero_max] at h
  rw [binaryRem_fold p a n Nat.lt_log2_self]; exact h

theorem two_pow_log2_le (p : ℕ) (hp : p ≠ 0) : 2 ^ p.log2 ≤ p := (Nat.le_log2 hp).mp le_rfl

theorem fieldMul_lt (p a b : ℕ) (hp : p ≠ 0) : fieldMul p a b < 2 ^ p.log2 := binaryRem_lt p _ hp


/-! ## `gfMul` -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor
/-!
# `localColor` on `Cmd` (q379, Part G): setup and neighbour-list facts

Register map of `colorOf` (base `g`, all registers `g .. g+50`; the enumerator `cfg` must
start at `cfg.r0 ≥ g + 51`):
* `g .. g+15` field context and scratch (`RamGF`), `g+16 g+17 g+18 g+19` = `D off K E` of
  `bitEvalW` (`D` is the digit array, `K` is kept there throughout);
* `g+24` `Q`, `g+25` `|x|`, `g+26` `J` (number of neighbours), `g+27` `α`, `g+28` `found`,
  `g+29` `ok`, `g+30` `bitEval(x,a)`, `g+31` `a`, `g+32` `j`, `g+33 g+35` loop `one`s,
  `g+34 g+36 g+38 g+39` scratch, `g+36` the result;
* `g+40 .. g+50` the block of the word utilities.
Arrays: `XA` (a copy of `x`), `DG` (digits: row `0` is `x`, row `m+1` neighbour `m`, stride `K`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The neighbour list -/

theorem mem_confusionNeighbors {q : ℕ} (t : ℕ) (x y : Word q) :
    y ∈ confusionNeighbors t x ↔ y ∈ nbrList t x := by
  unfold confusionNeighbors nbrList visits
  rw [List.mem_eraseDups, (List.mergeSort_perm _ _).mem_iff]

theorem confusionNeighbors_all {q : ℕ} (t : ℕ) (x : Word q) (f : Word q → Bool) :
    (confusionNeighbors t x).all f = (nbrList t x).all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  simp only [mem_confusionNeighbors]

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

/-! ## Enumeration: digits of every neighbour -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor2
/-!
# `localColor` on `Cmd` (q379, Part G): the search for the first separating point

Digit array `DG`: row `m` (offset `m * K`) holds the base-`Q` digits of `ids m`, `m ≤ J`.
`okAt … a` says `bitEval` at `a` separates row `0` from every row `j + 1`, `j < J`; the search
computes `α = ((List.range Q).find? okAt).getD 0` with a `found` flag (no early exit).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem bitEval_lt (Q p K W id a : ℕ) (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q)
    (hQW : Q ≤ 2 ^ W) : bitEval Q p K id a < 2 ^ W := by
  unfold bitEval
  have : ∀ (l : List ℕ) z, z < 2 ^ W → l.foldl (fun z i =>
      Nat.xor (fieldMul p z a) ((id / Q ^ i) % Q)) z < 2 ^ W := by
    intro l
    induction l with
    | nil => intro z hz; exact hz
    | cons i l ih =>
      intro z _
      apply ih
      exact Nat.xor_lt_two_pow
        (lt_of_lt_of_le (fieldMul_lt p _ _ hp) (le_trans (two_pow_log2_le p hp) hpW.le))
        (lt_of_lt_of_le (Nat.mod_lt _ hQ0) hQW)
  exact this _ 0 (by positivity)

section Search
variable (inp : ℕ → ℕ) (B : ℕ)

theorem find_range_lt (P : ℕ → Bool) (a v : ℕ) (h : (List.range a).find? P = some v) : v < a := by
  have := List.mem_of_find?_eq_some h
  simpa using this

end Search

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor3
/-!
# `colorOf`: the program computing `localColor t P p x` (q379, Part G)

Main theorem `colorOf_spec`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem bne_eq_decide_ne (a b : ℕ) : (a != b) = decide (a ≠ b) := by
  by_cases h : a = b <;> simp [h]

theorem all_range_getD {α : Type*} (l : List α) (d : α) (f : α → Bool) :
    (List.range l.length).all (fun j => f (l.getD j d)) = l.all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    have := h j (by simpa using hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  · intro h j hj
    simp only [List.mem_range] at hj
    rw [List.getD_eq_getElem _ _ hj]; exact h _ (List.getElem_mem hj)

/-- `localColor` in terms of `okAt` on `rowIds`. -/
theorem localColor_eq {q : ℕ} (t : ℕ) (P : Parameters) (p : ℕ) (x : Word q) :
    localColor t P p x =
      let α := ((List.range P.Q).find? (okAt P.Q p P.K (rowIds t x) (nbrList t x).length)).getD 0
      P.Q * α + bitEval P.Q p P.K (value x) α := by
  unfold localColor
  have : (fun a => (confusionNeighbors t x).all fun y =>
      decide (bitEval P.Q p P.K (value x) a ≠ bitEval P.Q p P.K (value y) a)) =
      okAt P.Q p P.K (rowIds t x) (nbrList t x).length := by
    funext a
    rw [confusionNeighbors_all, okAt, ← all_range_getD (nbrList t x) []]
    simp only [rowIds, bne_eq_decide_ne]
  simp only [this]

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor4
/-!
# `colorsAll`: the colour of `x` and of each of its neighbours (q379, Part G)

`colorsAll q t cfg1 cfg2 g X2 XA DG CLA`: `colorOf` (block `g .. g+50`, enumerator `cfg2`) on `x`
(result `g+51`), then the enumerator `cfg1` over `visits (2t) x`; for every visited `w` of length
`|x|` other than `x` (in visit order, duplicates kept: the list `nbrList t x`) it copies `w`
into `cfg2.buf (2t)`, runs `colorOf` and stores the colour at `CLA[J]`, `J := J + 1` (`g+52`).
Own registers `g+51 .. g+67`; `cfg2.r0 ≥ g + 68`, `cfg1.r0` above the registers of `cfg2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem localColor_lt_oai {q : ℕ} (t : ℕ) (P : Parameters) (p W : ℕ) (x : Word q) (hp : p ≠ 0)
    (hpW : p < 2 ^ W) (hQ0 : 0 < P.Q) (hQW : P.Q ≤ 2 ^ W) :
    localColor t P p x < P.Q * P.Q + 2 ^ W := by
  rw [localColor_eq]
  simp only
  set α := ((List.range P.Q).find? (okAt P.Q p P.K (rowIds t x) (nbrList t x).length)).getD 0
  have hα : α < P.Q := by
    rcases hf : (List.range P.Q).find? (okAt P.Q p P.K (rowIds t x) (nbrList t x).length) with _ | v
    · simp only [α, hf, Option.getD_none]; exact hQ0
    · simp only [α, hf, Option.getD_some]; exact find_range_lt _ _ _ hf
  have := bitEval_lt P.Q p P.K W (value x) α hp hpW hQ0 hQW
  have : P.Q * α ≤ P.Q * P.Q := Nat.mul_le_mul_left _ hα.le
  omega

/-! ## The program -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.localColor_lt_oai := @EditMulticoloring.Dev.Ram.localColor_lt_oai
