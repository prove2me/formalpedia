-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.pC5_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:02.086233+00:00
-- url     : https://prove2.me/submissions/782aa819-27f7-450e-96ca-dd0605f9a342

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_colorsAll_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_word
import Theorems.Thm_EditMulticoloring_Dev_Ram_goodW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_pC7_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne
import Theorems.Thm_EditMulticoloring_Dev_Ram_visits_le_visBound

section
-- module Solutions.EditMulticoloring.RamLib
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Program-proof library for `Cmd` (q379, Part L)

* `simp` lemmas for `Cmd.exec` / `Cmd.cost` of every constructor and convenience constructor;
* `HS.setR` (register update) and `HS.arr` lemmas;
* syntactic frames: `Cmd.wregs` (registers possibly written), `Cmd.reads`, `Cmd.emits`, `Cmd.stores`;
* monotonicity of `kappa` and `RAM.bits`;
* the general loop lemma `loop_spec`, the counted for-loop `forLoop` with `forLoop_spec`
  (invariant + cost) and its list-fold form `forLoop_fold`;
* `copyW`, a word copy between (array, offset) places.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## States -/

/-! ## Small rewriting helpers (use with `simp (disch := omega)`) -/

/-! ## `exec` and `cost` of the constructors -/

section ExecCost
variable (inp : ℕ → ℕ) (B : ℕ)

theorem exec_loop (a : ℕ) (c : Cmd) (s : HS) :
    (Cmd.loop a c).exec inp s = (c.exec inp)^[s.regs a] s := rfl

end ExecCost

/-! ## Monotonicity of the charges -/

/-! ## Syntactic frames -/

section Frames
variable (inp : ℕ → ℕ)

theorem iterate_induct {f : HS → HS} (P : HS → Prop) (h : ∀ s, P s → P (f s)) :
    ∀ (n : ℕ) (s : HS), P s → P (f^[n] s)
  | 0, _, hs => hs
  | n + 1, s, hs => by rw [Function.iterate_succ_apply]; exact iterate_induct P h n _ (h _ hs)

theorem exec_regs_of_not_mem (c : Cmd) {r : ℕ} (h : r ∉ c.wregs) (s : HS) :
    (c.exec inp s).regs r = s.regs r := by
  induction c generalizing s with
  | prim p =>
    cases p <;> simp_all [Cmd.wregs, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.wregs, List.mem_append, not_or] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.wregs, List.mem_append, not_or] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.wregs] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.regs r = s.regs r) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

theorem exec_cur_of_reads (c : Cmd) (h : c.reads = false) (s : HS) :
    (c.exec inp s).cur = s.cur := by
  induction c generalizing s with
  | prim p => cases p <;> simp_all [Cmd.reads, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.reads, Bool.or_eq_false_iff] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.reads, Bool.or_eq_false_iff] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.reads] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.cur = s.cur) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

theorem exec_out_of_emits (c : Cmd) (h : c.emits = false) (s : HS) :
    (c.exec inp s).out = s.out := by
  induction c generalizing s with
  | prim p => cases p <;> simp_all [Cmd.emits, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.emits, Bool.or_eq_false_iff] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.emits, Bool.or_eq_false_iff] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.emits] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.out = s.out) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

theorem exec_mem_of_stores (c : Cmd) (h : c.stores = false) (s : HS) :
    (c.exec inp s).mem = s.mem := by
  induction c generalizing s with
  | prim p => cases p <;> simp_all [Cmd.stores, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.stores, Bool.or_eq_false_iff] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.stores, Bool.or_eq_false_iff] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.stores] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.mem = s.mem) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

theorem exec_arr_of_stores (c : Cmd) (h : c.stores = false) (s : HS) (x i : ℕ) :
    (c.exec inp s).arr x i = s.arr x i := by
  simp [HS.arr, exec_mem_of_stores inp c h s]

end Frames

/-! ## Loops -/

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

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

theorem nbrList_length_le {q : ℕ} (t : ℕ) (x : Word q) :
    (nbrList t x).length ≤ (visits (2 * t) x).length := List.length_filter_le _ _

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

/-! ## Enumeration: digits of every neighbour -/

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

/-- The `.all` over the confusion neighbourhood, as a test over the indices of `nbrList`. -/
theorem confusionNeighbors_all_range {q : ℕ} (t : ℕ) (x : Word q) (f : Word q → Bool) :
    (confusionNeighbors t x).all f =
      (List.range (nbrList t x).length).all (fun j => f ((nbrList t x).getD j [])) := by
  rw [confusionNeighbors_all, all_range_getD]

/-! ## The program -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Part P (q379): the prime table

`primesW PR Mc S`: for every `m < regs Mc` (trial division), store the primes in increasing
order into array `regs PR`: afterwards `arr PR i = Nat.nth Nat.Prime i` for all
`i < Nat.count Nat.Prime (regs Mc)`, and register `S` holds that count.
With `regs Mc > (L + 2) * (2 * (Nat.log 2 (L + 2) + 3))` this covers every `i ≤ L`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ### A Chebyshev bound on the `N`-th prime (copied from the q373 record,
`Solutions/EditMulticoloring/EncoderRedundancyAux1.lean`, `nth_prime_le`). -/

theorem ramP_two_mul_add_one_le_two_pow : ∀ s : ℕ, 3 ≤ s → 2 * s + 1 ≤ 2 ^ s
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, _ => by norm_num
  | s + 4, _ => by
    have := ramP_two_mul_add_one_le_two_pow (s + 3) (by omega)
    rw [pow_succ]; omega

/-- A Chebyshev-type upper bound on the `N`-th prime (zero based). -/
theorem ramP_nth_prime_le (N : ℕ) :
    Nat.nth Nat.Prime N ≤ (N + 2) * (2 * (Nat.log 2 (N + 2) + 3)) := by
  set s := Nat.log 2 (N + 2) + 3 with hs
  set x := (N + 2) * (2 * s) with hx
  have h1 : N + 2 < 2 ^ s := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N + 2)
    calc N + 2 < 2 ^ (Nat.log 2 (N + 2) + 1) := this
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := ramP_two_mul_add_one_le_two_pow s (by omega)
  have h3 : x + 1 ≤ 2 ^ (2 * s) := by
    have : (N + 2) * (2 * s + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul h1.le h2
    rw [two_mul s, pow_add]
    have : (N + 2) * (2 * s + 1) = x + (N + 2) := by rw [hx]; ring
    omega
  have hx12 : 12 ≤ x := by
    have : 6 ≤ 2 * s := by omega
    calc 12 = 2 * 6 := by norm_num
      _ ≤ (N + 2) * (2 * s) := Nat.mul_le_mul (by omega) this
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlx1 : Real.log (x : ℝ) ≤ Real.log ((x : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have h4 : Real.log ((x : ℝ) + 1) ≤ (2 * s : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h3
  have h5 : ((N : ℝ) + 1) ≤ ((x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1)) / Real.log x := by
    rw [le_div_iff₀ hlx]
    have hxr : (x : ℝ) = ((N : ℝ) + 2) * ((2 * s : ℕ) : ℝ) := by rw [hx]; push_cast; ring
    have : ((N : ℝ) + 2) * Real.log ((x : ℝ) + 1) ≤ (x : ℝ) * Real.log 2 := by
      calc ((N : ℝ) + 2) * Real.log ((x : ℝ) + 1)
          ≤ ((N : ℝ) + 2) * (((2 * s : ℕ) : ℝ) * Real.log 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (x : ℝ) * Real.log 2 := by rw [hxr]; ring
    nlinarith
  have h6 := Chebyshev.pi_ge x
  have h7 : N < Nat.primeCounting x := by
    have : (N : ℝ) < (Nat.primeCounting x : ℝ) := by linarith
    exact_mod_cast this
  have h8 : Nat.nth Nat.Prime N < x + 1 := by
    apply Nat.nth_lt_of_lt_count
    rw [← Nat.primeCounting', ← Nat.primeCounting_eq_primeCounting'_succ] at *
    exact h7
  omega

/-- Indices below the count of primes below `M`. -/
theorem lt_count_prime_of_nth_lt {i M : ℕ} (h : Nat.nth Nat.Prime i < M) :
    i < Nat.count Nat.Prime M := by
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime i + 1) = i + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime,
      if_pos (Nat.prime_nth_prime i)]
  have h2 := Nat.count_monotone Nat.Prime (show Nat.nth Nat.Prime i + 1 ≤ M by omega)
  omega

theorem lt_count_prime_of_le {i L M : ℕ} (hi : i ≤ L)
    (hM : (L + 2) * (2 * (Nat.log 2 (L + 2) + 3)) < M) : i < Nat.count Nat.Prime M := by
  apply lt_count_prime_of_nth_lt
  have h1 : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime L :=
    Nat.nth_monotone Nat.infinite_setOfPred_prime hi
  have := ramP_nth_prime_le L
  omega

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams5
/-!
# Part P (q379): the parameters, part P (prime table, `h₂`, `h`) and part R (`q^h, ρ, q^ρ, m, k`)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem primeAt_lt_primeBound {i L : ℕ} (hi : i ≤ L) : primeAt i < primeBound L := by
  have := lt_count_prime_of_le (M := primeBound L) hi (by unfold primeBound; omega)
  exact Nat.nth_lt_of_lt_count this

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams6
/-!
# Part P (q379): `paramsW`, all fields of `parameters q t n`

`paramsW q t nR PR O` (with `nR, PR < O`, `n = regs nR`, `regs PR` an array id) leaves
`ParamsAt s' O q t n` (layout below), fills the prime table `arr (regs PR) i = primeAt i` for
`i ≤ L`, and writes only registers in `[O, O + 49)`.

Layout: `O+0 r, O+1 K, O+2 b, O+3 Q, O+4 B, O+5 L, O+6 W = b + 1, O+7 f = Nat.log q (L / 2),
O+8 J, O+9 h₁, O+10 h₂, O+11 h, O+12 q^h, O+13 ρ, O+14 q^ρ, O+15 m, O+16 k`,
where `b = ceilLog 2 (r * K + 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ### Size bounds of the outputs -/

theorem params_m_le (q t n : ℕ) : (parameters q t n).m ≤ n := Nat.sub_le _ _

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamDecode2
/-!
# The decoder, part 2: semantics, layout, frames, and the last levels of the candidate test
(q379, Part D)

Layout of the decoder (constant registers / arrays; `t`-dependent ones are functions of `t`):
* registers `0` = n, `1` = 1 (the prime-table array id), `2` = done flag (`decFlag`),
  `3` = q^h₂, `4` = q, `100 .. 116` the parameters (`ParamsAt _ 100`), `200 .. 299` scratch of
  the candidate test, `400 ..` the `colorsAll` block (`g = 400`: `400` = p, `403` = W, `418` = K,
  `424` = Q), enumerators `dC2c` (`r0 = 470`), `dC1 t` (`r0 = 490 + 6t`), `dC0 t` (`r0 = 510 + 12t`);
* arrays `1` the prime table, `2` the result, `3 4 5 6` = `X2 XA DG CLA` of `colorsAll`, `10 ..`
  enumerator arrays, `dINV t = 18 + 5t` the inverse table of the short code.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Semantics of `validate` and `decode` -/

theorem WordAt.takeD {q : ℕ} {s : HS} {X : ℕ} {w : Word q} (hw : WordAt s X 0 w) (m : ℕ) :
    WordAt s X 0 (w.take m) := by
  intro i hi
  rw [List.length_take] at hi
  rw [List.getElem_take]; exact hw i (by omega)

/-! ## Layout -/

theorem dPlace (t : ℕ) : CAPlace t (dC1 t) dC2c 400 3 4 5 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [dC1, dC2c] <;> omega

theorem SFr.trans {t : ℕ} {s1 s2 s3 : HS} (h1 : SFr t s1 s2) (h2 : SFr t s2 s3) : SFr t s1 s3 :=
  ⟨fun r hr => (h2.1 r hr).trans (h1.1 r hr), fun y i hy => (h2.2.1 y i hy).trans (h1.2.1 y i hy),
    h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem DOut.pre {q : ℕ} {t : ℕ} {st st1 st2 : HS} {res : Option (Word q)} (h1 : SFr t st st1)
    (h2 : st1.regs 2 = st.regs 2) (h : DOut t st1 st2 res) : DOut t st st2 res :=
  ⟨h1.trans h.1, fun hr => (h.2.1 hr).trans h2, h.2.2⟩

theorem DOut.none_of_SFr {q : ℕ} {t : ℕ} {st st' : HS} (h1 : SFr t st st')
    (h2 : st'.regs 2 = st.regs 2) : DOut (q := q) t st st' none :=
  ⟨h1, fun _ => h2, fun r hr => by cases hr⟩

/-- A block writing only scratch registers `[200, 400) ∪ [401, 470)`-type registers, without stores. -/
theorem sfr_of_block (inp : ℕ → ℕ) (t : ℕ) (c : Cmd) (hw : ∀ r ∈ c.wregs, 200 ≤ r ∧ r < 400)
    (hs : c.stores = false) (hr : c.reads = false) (he : c.emits = false) (st : HS) :
    SFr t st (c.exec inp st) ∧ (c.exec inp st).regs 2 = st.regs 2 := by
  have key : ∀ r, (r < 200 ∨ 400 ≤ r) → (c.exec inp st).regs r = st.regs r := by
    intro r h
    apply exec_regs_of_not_mem
    intro hm; have := hw r hm; omega
  refine ⟨⟨fun r hr => key r ?_, fun y i _ => exec_arr_of_stores inp c hs st y i,
    exec_cur_of_reads inp c hr st, exec_out_of_emits inp c he st⟩, key 2 (by omega)⟩
  unfold KeptR at hr; omega

theorem sfr_of_regs {t : ℕ} {st st' : HS} (hR : ∀ r, (KeptR t r ∨ r = 2) → st'.regs r = st.regs r)
    (hM : ∀ y i, KeptA t y → st'.arr y i = st.arr y i) (hc : st'.cur = st.cur)
    (ho : st'.out = st.out) : SFr t st st' ∧ st'.regs 2 = st.regs 2 :=
  ⟨⟨fun r hr => hR r (Or.inl hr), hM, hc, ho⟩, hR 2 (Or.inr rfl)⟩

theorem DCtx.of_SFr {q t n p : ℕ} {st st' : HS} (h : DCtx q t n p st) (hf : SFr t st st') :
    DCtx q t n p st' := by
  have R : ∀ r, r < 200 → r ≠ 2 → st'.regs r = st.regs r := fun r h1 h2 =>
    hf.1 r (Or.inl ⟨h1, h2⟩)
  have A1 : ∀ i, st'.arr 1 i = st.arr 1 i := fun i => hf.2.1 1 i (Or.inl rfl)
  have AI : ∀ i, st'.arr (dINV t) i = st.arr (dINV t) i := fun i =>
    hf.2.1 _ i (Or.inr (by unfold dINV; omega))
  obtain ⟨h0, h1, h3, h4, ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16⟩,
    g0, g3, g18, g24, prt, inv, invb⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [R _ (by omega) (by omega)]; assumption)
    | (rw [hf.1 _ (by unfold KeptR; omega)]; assumption)
    | skip
  · intro i hi; rw [A1]; exact prt i hi
  · intro z hz; simp only [AI]; exact inv z hz
  · intro u hu; rw [AI]; exact invb u hu

/-! ## Size bounds -/

section Levels
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Level 8: store the result `x ++ repr q (k - m) j` and set the done flag -/

/-! ## Level 7: count the good indices below `i`, compare with `J`, store -/

theorem goodP_eq_localGood {q : ℕ} (t : ℕ) (P : Parameters) (p : ℕ) (x : Word q) (i : ℕ)
    (cl : ℕ → ℕ) (hcl : ∀ ℓ (h : ℓ < (nbrList t x).length), cl ℓ = localColor t P p (nbrList t x)[ℓ]) :
    goodP (localColor t P p x) (primeAt i) cl (nbrList t x).length = localGood t P p x i := by
  unfold localGood goodP
  rw [confusionNeighbors_all_range]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  apply forall_congr'; intro ℓ
  apply imp_congr_right; intro hℓ
  rw [List.mem_range] at hℓ
  rw [hcl ℓ hℓ, List.getD_eq_getElem _ _ hℓ]

/-! ## Level 6: compare `η` with the colour of `x` modulo `primeAt i` -/

theorem pC6_spec {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
    (hcol : ∀ y : Word q, localColor t (parameters q t n) p y < (parameters q t n).Q * (parameters q t n).Q + dTW q t n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (i η : ℕ) (hi : st.regs 213 = i) (hiL : i < (parameters q t n).L)
    (hη : st.regs 214 = η) (hηp : η < primeAt i) (hpi : st.regs 215 = primeAt i)
    (hcx : st.regs 451 = localColor t (parameters q t n) p (w.take (parameters q t n).m))
    (hV : st.regs 452 = (nbrList t (w.take (parameters q t n).m)).length)
    (hCL : ∀ ℓ (h : ℓ < (nbrList t (w.take (parameters q t n).m)).length),
      st.arr 6 ℓ = localColor t (parameters q t n) p (nbrList t (w.take (parameters q t n).m))[ℓ]) :
    DOut t st ((pC6 t).exec inp st)
      (if η ≠ localColor t (parameters q t n) p (w.take (parameters q t n).m) % primeAt i then none
       else r7 t (parameters q t n) p (w.take (parameters q t n).m) i) ∧
    (pC6 t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 7 * n + 7 * (parameters q t n).k + 45) *
      kappa B (RAM.bits (DM q t n)) := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  set x := w.take P.m with hx
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have hpb := primeAt_lt_primeBound (L := P.L) (i := i) hiL.le
  have hcx0 := hcol x
  set c := localColor t P p x % primeAt i with hcdef
  have hcle : c ≤ localColor t P p x := Nat.mod_le _ _
  set A := seqs [ar .mod 216 451 215, ar .sub 217 216 214, ar .sub 218 214 216, ar .add 217 217 218]
    with hA
  set s1 := A.exec inp st with hs1
  have hfr := sfr_of_block inp t A (by
      intro r hr; simp only [hA, seqs, Cmd.wregs, ar, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.nil_append, List.append_nil] at hr; omega)
    rfl rfl rfl st
  have v217 : s1.regs 217 = (c - η) + (η - c) := by
    simp (disch := omega) [hs1, hA, upd_ne, hcx, hpi, hη, hcdef]
  have c1 : A.cost inp B st ≤ 4 * κ := by
    simp (disch := omega) only [hA, cost_seqs_cons, cost_seqs_nil, cost_ar, exec_seqs_cons,
      exec_ar, HS.setR_regs, upd_ne, upd_eq, hcx, hpi, hη, arith_mod, arith_sub, arith_add]
    rw [← hcdef]
    have := kb (localColor t P p x + primeAt i) (by omega)
    have := kb (c + η) (by omega)
    have := kb (η + c) (by omega)
    have := kb (c - η + (η - c)) (by omega)
    omega
  have hex : (pC6 t).exec inp st = (Cmd.ifz 217 (pC7 t) .skip).exec inp s1 := rfl
  have hco : (pC6 t).cost inp B st = A.cost inp B st + (Cmd.ifz 217 (pC7 t) .skip).cost inp B s1 := rfl
  have hk := kb ((c - η) + (η - c)) (by omega)
  rw [hex, hco]
  by_cases heq : η = c
  · have hz : s1.regs 217 = 0 := by rw [v217]; omega
    have hc1 := hc.of_SFr hfr.1
    have hw1 : WordAt s1 (dC0 t).a0 0 w := hw.congr (fun i _ => hfr.1.2.1 _ _ (Or.inr (by simp [dC0])))
    have R : ∀ r, (r < 216 ∨ 219 ≤ r) → s1.regs r = st.regs r := by
      intro r hr; simp (disch := omega) [hs1, hA, upd_ne]
    obtain ⟨D1, D2⟩ := pC7_spec inp B hq H3 hcol s1 hc1 w hw1 hwl i (by rw [R _ (by omega), hi]) hiL
      (by rw [R _ (by omega), hcx]) (by rw [R _ (by omega), hV])
      (fun ℓ hℓ => by rw [show s1.arr 6 ℓ = st.arr 6 ℓ by simp [HS.arr, hs1, exec_mem_of_stores inp A rfl]]
                      exact hCL ℓ hℓ)
    have D2' : (pC7 t).cost inp B s1 ≤ ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 40) * κ := D2
    rw [if_neg (by omega)]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_pos hz]; exact DOut.pre hfr.1 hfr.2 D1
    · rw [cost_ifz, if_pos hz]
      have h3 : ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 45) * κ =
        ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 40) * κ + 5 * κ := by ring
      rw [h3, v217]; omega
  · have hz : s1.regs 217 ≠ 0 := by rw [v217]; omega
    rw [if_pos heq]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_neg hz]; exact DOut.none_of_SFr hfr.1 hfr.2
    · rw [cost_ifz, if_neg hz, cost_skip, v217]
      have h3 : ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 45) * κ =
        ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 40) * κ + 5 * κ := by ring
      rw [h3]; omega

/-! ## Level 5: the colours (`colorsAll`), the test `localGood x i` -/

set_option maxHeartbeats 1600000 in
theorem pC5_spec_oai {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
    (hcol : ∀ y : Word q, localColor t (parameters q t n) p y < (parameters q t n).Q * (parameters q t n).Q + dTW q t n)
    (hp : p ≠ 0) (hpW : p < dTW q t n) (hQ0 : 0 < (parameters q t n).Q)
    (hQW : (parameters q t n).Q ≤ dTW q t n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (i η : ℕ) (hi : st.regs 213 = i) (hiL : i < (parameters q t n).L)
    (hη : st.regs 214 = η) (hηp : η < primeAt i) (hpi : st.regs 215 = primeAt i) :
    DOut t st ((pC5 q t).exec inp st) (vTail t (parameters q t n) p (w.take (parameters q t n).m) i η) ∧
    (pC5 q t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 14 * n +
      7 * (parameters q t n).k + 11 * dVb q t n + 70) * kappa B (RAM.bits (DM q t n)) + caCost q t n B := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  set x := w.take P.m with hx
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hmn : P.m ≤ n := params_m_le q t n
  have hm115 : st.regs 115 = P.m := hc.par.hm
  have ha0 : (dC0 t).a0 = 14 + 4 * t := rfl
  have hxl : x.length = P.m := by rw [hx, List.length_take]; omega
  have hpb := primeAt_lt_primeBound (L := P.L) (i := i) hiL.le
  -- block 1
  set A1 := seqs [lit 220 (dC0 t).a0, lit 221 0, lit 222 (13 + 4 * t), lit 223 0, cp 224 115] with hA1
  set s1 := A1.exec inp st with hs1
  have r1 : ∀ r, (r < 220 ∨ 225 ≤ r) → s1.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs1, hA1, upd_ne]
  have m1 : s1.mem = st.mem := by simp [hs1, hA1]
  have v220 : s1.regs 220 = 14 + 4 * t := by simp (disch := omega) [hs1, hA1, upd_ne, ha0]
  have v221 : s1.regs 221 = 0 := by simp (disch := omega) [hs1, hA1, upd_ne]
  have v222 : s1.regs 222 = 13 + 4 * t := by simp (disch := omega) [hs1, hA1, upd_ne]
  have v223 : s1.regs 223 = 0 := by simp (disch := omega) [hs1, hA1, upd_ne]
  have v224 : s1.regs 224 = P.m := by simp (disch := omega) [hs1, hA1, upd_ne, hm115]
  have c1 : A1.cost inp B st ≤ 5 * κ := by
    simp (disch := omega) only [hA1, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, hm115, ha0]
    have := kb (14 + 4 * t) (by omega)
    have := kb 0 (by omega)
    have := kb (13 + 4 * t) (by omega)
    have := kb P.m (by omega)
    omega
  have hw1 : WordAt s1 (14 + 4 * t) 0 x := by
    rw [← ha0]; exact (hw.takeD P.m).congr (fun i _ => by simp [HS.arr, m1])
  have hnd : [220, 221, 222, 223, 224, 225, 226, 227, 228].Nodup := by decide
  have hSD : s1.regs 220 ≠ s1.regs 222 := by rw [v220, v222]; omega
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := copyW_spec inp B 220 221 222 223 224 225 226 227 228 s1 hnd hSD
    q (DM q t n) (fun i hi => by rw [v220, v221]; rw [v224] at hi; exact (hw1.lt i (by omega)).le)
    (by rw [v220, v221, v222, v223, v224]; omega)
  have hx2 := copyW_word inp 220 221 222 223 224 225 226 227 228 s1 x hnd hSD
    (by rw [v220, v221]; exact hw1) (by rw [v224, hxl])
  rw [v222, v223] at hx2 b2
  rw [v224] at b6
  set s2 := (copyW 220 221 222 223 224 225 226 227 228).exec inp s1 with hs2
  have r2 : ∀ r, (r < 220 ∨ 229 ≤ r) → s2.regs r = st.regs r := by
    intro r hr; rw [b3 r (by omega) (by omega) (by omega) (by omega), r1 r (by omega)]
  set s3 := s2.setR (508 + 12 * t) (s2.regs 115) with hs3
  have r3 : ∀ r, (r < 220 ∨ 229 ≤ r) → r ≠ 508 + 12 * t → s3.regs r = st.regs r := by
    intro r h1 h2; simp only [hs3, HS.setR_regs]; rw [upd_ne h2, r2 r h1]
  have c3 : (cp (508 + 12 * t) 115).cost inp B s2 ≤ κ := by
    simp only [cost_cp]; rw [r2 _ (by omega), hm115]; exact kb _ (by omega)
  -- colorsAll
  have hlenR : (dC1 t).lenR (2 * t) = 508 + 12 * t := by simp [dC1]; ring
  have hbufR : (dC1 t).buf (2 * t) = 13 + 4 * t := by simp [dC1]; ring
  have hlen3 : s3.regs ((dC1 t).lenR (2 * t)) = x.length := by
    rw [hlenR, hxl]; simp [hs3, r2 115 (by omega), hm115]
  have hx3 : WordAt s3 ((dC1 t).buf (2 * t)) 0 x := by
    rw [hbufR]; exact hx2.congr (fun i _ => rfl)
  have hW : dTW q t n = 2 ^ dW q t n := rfl
  have hVb : visBound q t x.length ≤ dVb q t n := by rw [hxl]; exact le_rfl
  have hMs : p * 2 ^ (2 * dW q t n) + 6 * 2 ^ (2 * dW q t n) + 5 + (dVb q t n + 2) * P.K + dVb q t n ≤
      dMs q t n := by
    have : p * 2 ^ (2 * dW q t n) ≤ dTW q t n * 2 ^ (2 * dW q t n) := Nat.mul_le_mul_right _ hpW.le
    show _ ≤ dTW q t n * 2 ^ (2 * dW q t n) + 6 * 2 ^ (2 * dW q t n) + 5 + (dVb q t n + 2) * P.K +
      dVb q t n
    omega
  have hMb : q ^ x.length + 2 * q + 2 * (dC1 t).a0 + 2 * t + 3 + 4 + 5 + 6 + 2 * x.length + P.Q +
      (dVb q t n + 1) * P.K + dVb q t n + 2 * 2 ^ (2 * dW q t n) + 2 ≤ dMb q t n := by
    rw [hxl]
    show _ ≤ q ^ P.m + 2 * q + 2 * (12 + 2 * t) + 2 * t + 3 + 4 + 5 + 6 +
      2 * P.m + P.Q + (dVb q t n + 1) * P.K + dVb q t n + 2 * 2 ^ (2 * dW q t n) + 2
    simp [dC1]
  have e400 : s3.regs 400 = p := by rw [r3 _ (by omega) (by omega)]; exact hc.g0
  have e403 : s3.regs (400 + 3) = dW q t n := by rw [r3 _ (by omega) (by omega)]; exact hc.g3
  have e418 : s3.regs (400 + 18) = P.K := by rw [r3 _ (by omega) (by omega)]; exact hc.g18
  have e424 : s3.regs (400 + 24) = P.Q := by rw [r3 _ (by omega) (by omega)]; exact hc.g24
  obtain ⟨a51, a52, aCL, areg, aarr, -, -, acur, aout, acost⟩ := colorsAll_spec inp B t (dC1 t) dC2c
    400 3 4 5 6 x s3 p (dW q t n) P.Q P.K (dVb q t n) (dMs q t n) (dMb q t n) (dPlace t)
    e400 e403 e418 e424 hlen3 hx3 hp (by rw [← hW]; exact hpW) hQ0 (by rw [← hW]; exact hQW) hVb hMs hMb
  set s4 := (colorsAll q t (dC1 t) dC2c 400 3 4 5 6).exec inp s3 with hs4
  have nR1 : ∀ r, 510 + 12 * t ≤ r → ¬ (dC1 t).ownsReg (2 * t) r := fun r hr h => by
    simp only [EnumCfg.ownsReg, dC1] at h; omega
  have h1r0 : (dC1 t).r0 = 490 + 6 * t := rfl
  have r4 : ∀ r, (r < 220 ∨ (229 ≤ r ∧ r < 401) ∨ r = 403 ∨ r = 418 ∨ r = 424 ∨ 510 + 12 * t ≤ r) →
      s4.regs r = st.regs r := by
    intro r hr
    rw [areg r (by omega) (by intro hh; simp only [EnumCfg.ownsReg, dC1] at hh; omega)]
    exact r3 r (by omega) (by omega)
  have arr4 : ∀ y i, KeptA t y → s4.arr y i = st.arr y i := by
    intro y i hy
    unfold KeptA at hy
    rw [aarr y i (by omega) (by omega) (by omega) (by omega)
      (by intro hh; simp only [EnumCfg.ownsArr, dC2c] at hh; omega)
      (by intro hh; simp only [EnumCfg.ownsArr, dC1] at hh; omega)]
    show s2.arr y i = st.arr y i
    rw [b2 y i (by omega)]; simp [HS.arr, m1]
  have cx4 : s4.regs 451 = localColor t P p x := a51 P rfl rfl
  have V4 : s4.regs 452 = (nbrList t x).length := a52
  have CL4 : ∀ ℓ (h : ℓ < (nbrList t x).length), s4.arr 6 ℓ = localColor t P p (nbrList t x)[ℓ] :=
    fun ℓ h => aCL ℓ h P rfl rfl
  have cur4 : s4.cur = st.cur := by rw [acur]; simp [hs3, b4, hs1, hA1]
  have out4 : s4.out = st.out := by rw [aout]; simp [hs3, b5, hs1, hA1]
  -- goodW
  have hVbx : (nbrList t x).length ≤ dVb q t n :=
    (nbrList_length_le t x).trans ((visits_le_visBound t x).trans hVb)
  have hcx0 := hcol x
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := goodW_spec inp B 230 215 451 452 6 s4
    (P.Q * P.Q + dTW q t n) (DM q t n) (by omega) (by omega) (by omega)
    (fun ℓ hℓ => by rw [V4] at hℓ; rw [CL4 ℓ hℓ]; exact (hcol _).le)
    (by rw [V4, cx4, r4 _ (by omega), hpi]; omega)
  rw [V4, cx4, r4 215 (by omega), hpi] at g1
  rw [V4] at g6
  have hgood : goodP (localColor t P p x) (primeAt i) (s4.arr 6) (nbrList t x).length = localGood t P p x i :=
    goodP_eq_localGood t P p x i (s4.arr 6) CL4
  rw [hgood] at g1
  set s5 := (goodW 230 215 451 452 6).exec inp s4 with hs5
  have hfr5 := sfr_of_regs (t := t) (st := st) (st' := s5)
    (fun r hr => by
      unfold KeptR at hr
      rw [g2 r (by omega)]
      exact r4 r (by omega))
    (fun y i hy => by rw [show s5.arr y i = s4.arr y i by simp [HS.arr, g3]]; exact arr4 y i hy)
    (by rw [g4, cur4]) (by rw [g5, out4])
  have hex : (pC5 q t).exec inp st = (Cmd.ifz 230 .skip (pC6 t)).exec inp s5 := rfl
  have hco : (pC5 q t).cost inp B st = A1.cost inp B st +
      ((copyW 220 221 222 223 224 225 226 227 228).cost inp B s1 +
      ((cp (508 + 12 * t) 115).cost inp B s2 + ((colorsAll q t (dC1 t) dC2c 400 3 4 5 6).cost inp B s3 +
      ((goodW 230 215 451 452 6).cost inp B s4 + ((Cmd.ifz 230 .skip (pC6 t)).cost inp B s5 + 0))))) := rfl
  have acost' : (colorsAll q t (dC1 t) dC2c 400 3 4 5 6).cost inp B s3 ≤ caCost q t n B := by
    refine acost.trans (le_of_eq ?_)
    rw [hxl]; rfl
  have g6' : (goodW 230 215 451 452 6).cost inp B s4 ≤ (11 * dVb q t n + 6) * κ :=
    g6.trans (Nat.mul_le_mul_right _ (by omega))
  have b6' : (copyW 220 221 222 223 224 225 226 227 228).cost inp B s1 ≤ (7 * n + 3) * κ :=
    b6.trans (Nat.mul_le_mul_right _ (by omega))
  have hk0 := kb 0 (by omega)
  have hk1 := kb 1 (by omega)
  rw [hex, hco]
  unfold vTail
  by_cases hg : localGood t P p x i = true
  · have hz : s5.regs 230 ≠ 0 := by rw [g1, if_pos hg]; omega
    have hc5 := hc.of_SFr hfr5.1
    have hw5 : WordAt s5 (dC0 t).a0 0 w := hw.congr (fun i _ => hfr5.1.2.1 _ _ (Or.inr (by simp [dC0])))
    have R5 : ∀ r, (r < 220 ∨ (238 ≤ r ∧ r < 401)) → s5.regs r = st.regs r := fun r h => by
      rw [g2 r (by omega)]; exact r4 r (by omega)
    obtain ⟨D1, D2⟩ := pC6_spec inp B hq H3 hcol s5 hc5 w hw5 hwl i η (by rw [R5 _ (by omega), hi]) hiL
      (by rw [R5 _ (by omega), hη]) hηp (by rw [R5 _ (by omega), hpi])
      (by rw [g2 _ (by omega), cx4]) (by rw [g2 _ (by omega), V4])
      (fun ℓ hℓ => by rw [show s5.arr 6 ℓ = s4.arr 6 ℓ by simp [HS.arr, g3]]; exact CL4 ℓ hℓ)
    have D2' : (pC6 t).cost inp B s5 ≤ ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 45) * κ := D2
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_neg hz]
      have : (if (!localGood t P p x i || decide (η ≠ localColor t P p x % primeAt i)) = true then none
          else r7 t P p x i) =
          (if η ≠ localColor t P p x % primeAt i then none else r7 t P p x i) := by
        simp [hg]
      simp only [Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq] at this ⊢
      simp only [hg, Bool.true_eq_false, false_or]
      exact DOut.pre hfr5.1 hfr5.2 D1
    · rw [cost_ifz, if_neg hz]
      have := kb (s5.regs 230) (by rw [g1]; split_ifs <;> omega)
      have h3 : ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 70) * κ =
        5 * κ + (7 * n + 3) * κ + κ + (11 * dVb q t n + 6) * κ + κ +
        ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 45) * κ + 9 * κ := by ring
      rw [h3]; omega
  · have hz : s5.regs 230 = 0 := by rw [g1, if_neg hg]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_pos hz]
      have hg' : localGood t P p x i = false := by simpa using hg
      simp only [hg', Bool.not_false, Bool.true_or, if_true]
      exact DOut.none_of_SFr hfr5.1 hfr5.2
    · rw [cost_ifz, if_pos hz, cost_skip, hz]
      have h3 : ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 70) * κ =
        5 * κ + (7 * n + 3) * κ + κ + (11 * dVb q t n + 6) * κ + κ +
        ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 54) * κ := by ring
      rw [h3]
      have := Nat.zero_le (((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 54) * κ)
      omega

/-! ## Level 4: `pi := PR[i]`, test `η < pi` -/

/-! ## Level 3: `i := idx / q^h₂`, `η := idx % q^h₂`, test `i < L` -/

/-! ## Level 2: `idx := INV - 1`, test `idx < q^h` -/

/-! ## The candidate test: value of the tail, `INV` lookup -/

end Levels

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.pC5_spec_oai := @EditMulticoloring.Dev.Ram.pC5_spec_oai
