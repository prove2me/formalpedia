-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.encD_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:44.930322+00:00
-- url     : https://prove2.me/submissions/e883fb14-14ff-4fb4-ae02-11623fbeda00

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le

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

theorem kappa_mono {B B' W W' : ℕ} (hB : B ≤ B') (hW : W ≤ W') : kappa B W ≤ kappa B' W' := by
  unfold kappa
  have : (W + 2) ^ 2 ≤ (W' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem kappa_mono_right (B : ℕ) {W W' : ℕ} (hW : W ≤ W') : kappa B W ≤ kappa B W' :=
  kappa_mono le_rfl hW

theorem kappa_zero_le (B M : ℕ) : kappa B 0 ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (Nat.zero_le _)

/-! ## Syntactic frames -/

/-! ## Loops -/

section Loops
variable (inp : ℕ → ℕ) (B : ℕ)

/-- `loop a c`, with an invariant indexed by the number of completed iterations, and a
per-iteration cost bound. -/
theorem loop_spec (a : ℕ) (c : Cmd) (s : HS) (P : ℕ → HS → Prop) (C : ℕ → ℕ)
    (h0 : P 0 s)
    (hstep : ∀ k < s.regs a, ∀ st, P k st → P (k + 1) (c.exec inp st) ∧ c.cost inp B st ≤ C k) :
    P (s.regs a) ((Cmd.loop a c).exec inp s) ∧
    (Cmd.loop a c).cost inp B s ≤
      (s.regs a + 2) * kappa B (RAM.bits (s.regs a)) + ∑ k ∈ Finset.range (s.regs a), C k := by
  set N := s.regs a with hN
  have key : ∀ v k st, k + v = N → P k st →
      P N ((c.exec inp)^[v] st) ∧
      loopCost B (c.exec inp) (c.cost inp B) v st ≤
        (v + 1) * kappa B (RAM.bits N) + ∑ j ∈ Finset.range v, C (k + j) := by
    intro v
    induction v with
    | zero =>
      intro k st hk hP
      simp only [Nat.add_zero] at hk
      subst hk
      refine ⟨hP, ?_⟩
      simp only [loopCost, Finset.range_zero, Finset.sum_empty, zero_add, one_mul, add_zero]
      exact kappa_zero_le B _
    | succ v ih =>
      intro k st hk hP
      have hkN : k < N := by omega
      obtain ⟨hP1, hc⟩ := hstep k hkN st hP
      obtain ⟨hP2, hc2⟩ := ih (k + 1) (c.exec inp st) (by omega) hP1
      refine ⟨by rw [Function.iterate_succ_apply]; exact hP2, ?_⟩
      simp only [loopCost]
      have hκ : kappa B (RAM.bits (v + 1)) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
      rw [Finset.sum_range_succ']
      have : ∑ j ∈ Finset.range v, C (k + 1 + j) = ∑ j ∈ Finset.range v, C (k + (j + 1)) := by
        apply Finset.sum_congr rfl; intro j _; congr 1; omega
      rw [this] at hc2
      simp only [Nat.add_zero] at *
      nlinarith
  obtain ⟨h1, h2⟩ := key N 0 s (by omega) h0
  refine ⟨by rw [exec_loop]; exact h1, ?_⟩
  simp only [Cmd.cost]
  simp only [zero_add] at h2
  rw [← hN]
  nlinarith

/-- The for-loop lemma: invariant `P k` after `k` iterations (the counter register `i` holds
`k` at the start of iteration `k`, the body must keep it), and cost. -/
theorem forLoop_spec (i n one : ℕ) (body : Cmd) (s : HS) (hni : n ≠ i) (hio : i ≠ one)
    (P : ℕ → HS → Prop) (C : ℕ → ℕ)
    (h0 : P 0 (s.setR i 0))
    (hstep : ∀ k < s.regs n, ∀ st, P k st → st.regs i = k →
      (body.exec inp st).regs i = k ∧
      P (k + 1) (((body.exec inp st).setR one 1).setR i (k + 1)) ∧
      body.cost inp B st ≤ C k) :
    P (s.regs n) ((forLoop i n one body).exec inp s) ∧
    (forLoop i n one body).cost inp B s ≤
      3 * (s.regs n + 1) * kappa B (RAM.bits (s.regs n)) + ∑ k ∈ Finset.range (s.regs n), C k := by
  set N := s.regs n with hN
  have hN' : (s.setR i 0).regs n = N := by simp [hni, hN]
  have L := loop_spec inp B n (.seq body (.seq (lit one 1) (ar .add i i one))) (s.setR i 0)
    (fun k st => P k st ∧ st.regs i = k) (fun k => C k + 2 * kappa B (RAM.bits N))
    ⟨h0, by simp⟩ (by
      intro k hk st ⟨hP, hi⟩
      rw [hN'] at hk
      obtain ⟨hb1, hb2, hb3⟩ := hstep k hk st hP hi
      have hset : (Function.update (body.exec inp st).regs one 1) i +
          (Function.update (body.exec inp st).regs one 1) one = k + 1 := by
        simp [hio, hb1]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [exec_seq, exec_lit, exec_ar, arith_add, HS.setR_regs]
        rw [hset]; exact hb2
      · simp [hio, hb1]
      · simp only [cost_seq, cost_lit, cost_ar, exec_lit, HS.setR_regs]
        rw [Function.update_apply, if_neg hio, hb1, Function.update_apply, if_pos rfl]
        have e1 : kappa B (RAM.bits 1) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
        have e2 : kappa B (RAM.bits (k + 1)) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
        omega)
  rw [hN'] at L
  obtain ⟨⟨L1, -⟩, L2⟩ := L
  refine ⟨L1, ?_⟩
  simp only [forLoop, cost_seq, cost_lit]
  rw [Finset.sum_add_distrib] at L2
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at L2
  have e0 : kappa B (RAM.bits 0) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
  simp only [exec_lit] at *
  rw [hN'] at *
  nlinarith

end Loops

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

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
-- module Solutions.EditMulticoloring.RamEncode2
/-!
# The encoder program (q379, Part E), part 2: the good-index loop (phase D)

`encD` scans `i < L`; for each `i` it computes `good_i := ∀ ℓ < V, CL[ℓ] % PR[i] ≠ Cx % PR[i]`
(inner loop), and sets `sel := i` when `good_i` and the number `c` of good indices before `i`
equals `j`.  Result: `sel = ((range L).filter good)[j]?.getD L`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- The `j`-th element of a filtered range, one step at a time. -/
theorem filter_range_getD_succ (G : ℕ → Bool) (j L k : ℕ) :
    (((List.range (k + 1)).filter G)[j]?).getD L =
      if G k = true ∧ ((List.range k).filter G).length = j then k
      else (((List.range k).filter G)[j]?).getD L := by
  rw [List.range_succ, List.filter_append]
  by_cases hG : G k = true
  · have : [k].filter G = [k] := by simp [hG]
    rw [this, List.getElem?_append]
    by_cases hj : j < ((List.range k).filter G).length
    · rw [if_pos hj, if_neg (by omega), List.getElem?_eq_getElem hj]
    · rw [if_neg hj]
      by_cases hj' : ((List.range k).filter G).length = j
      · rw [if_pos ⟨hG, hj'⟩]; subst hj'; simp
      · rw [if_neg (by tauto)]
        rw [List.getElem?_eq_none (show [k].length ≤ j - ((List.range k).filter G).length by
          simp only [List.length_singleton]; omega), List.getElem?_eq_none (by omega)]
  · have : [k].filter G = [] := by simp [hG]
    rw [this, List.append_nil, if_neg (by tauto)]

theorem filter_range_length_succ (G : ℕ → Bool) (k : ℕ) :
    ((List.range (k + 1)).filter G).length =
      ((List.range k).filter G).length + (if G k = true then 1 else 0) := by
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases hG : G k = true <;> simp [hG]

section PhaseD
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encInner_spec (st : HS) (cl pr cxm A : ℕ) (hr17 : st.regs 17 = 6) (hr12 : st.regs 12 = pr)
    (hr13 : st.regs 13 = cxm) (hcl : st.arr 6 (st.regs 10) = cl)
    (hA : 6 + st.regs 10 + cl + pr + cxm ≤ A) :
    let st' := encInner.exec inp st
    st'.regs 7 = (if cl % pr = cxm then 0 else st.regs 7) ∧
    (∀ r, r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 16 → st'.regs r = st.regs r) ∧
    st'.mem = st.mem ∧ st'.cur = st.cur ∧ st'.out = st.out ∧
    encInner.cost inp B st ≤ 7 * kappa B (RAM.bits A) := by
  intro st'
  have hmod : cl % pr ≤ cl := Nat.mod_le _ _
  have hd : (cl % pr - cxm) + (cxm - cl % pr) = 0 ↔ cl % pr = cxm := by omega
  set s5 := ((((st.setR 14 cl).setR 14 (cl % pr)).setR 15 (cl % pr - cxm)).setR 16 (cxm - cl % pr)).setR 15
        ((cl % pr - cxm) + (cxm - cl % pr)) with hs5
  have hst' : st' = (Cmd.ifz 15 (lit 7 0) .skip).exec inp s5 := by
    simp only [st', encInner, exec_seqs_cons, exec_seqs_nil, exec_ald, exec_ar, arith_mod, arith_sub,
      arith_add, HS.setR_regs, hr17, hcl, HS.setR_arr]
    simp [Function.update_apply, hr12, hr13, hr17, hcl, hs5]
  have h15 : s5.regs 15 = (cl % pr - cxm) + (cxm - cl % pr) := by simp [hs5]
  have hr : ∀ r, r ≠ 14 → r ≠ 15 → r ≠ 16 → s5.regs r = st.regs r := by
    intro r h1 h2 h3; simp [hs5, Function.update_apply, h1, h2, h3]
  have hex : st' = if cl % pr = cxm then s5.setR 7 0 else s5 := by
    rw [hst']; simp only [exec_ifz, h15]
    by_cases h : cl % pr = cxm
    · rw [if_pos (hd.mpr h), if_pos h]; rfl
    · rw [if_neg (fun h' => h (hd.mp h')), if_neg h]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hex]; split_ifs
    · simp
    · exact hr 7 (by omega) (by omega) (by omega)
  · intro r h1 h2 h3 h4
    rw [hex]; split_ifs
    · simp only [HS.setR_regs]; rw [Function.update_of_ne h1]; exact hr r h2 h3 h4
    · exact hr r h2 h3 h4
  · rw [hex]; split_ifs <;> simp [hs5]
  · rw [hex]; split_ifs <;> simp [hs5]
  · rw [hex]; split_ifs <;> simp [hs5]
  · simp only [encInner, cost_seqs_cons, cost_seqs_nil, cost_ald, cost_ar, cost_ifz, cost_lit,
      cost_skip, exec_seqs_cons, exec_ald, exec_ar, arith_mod, arith_sub, arith_add, HS.setR_regs,
      HS.setR_arr, hr17, hcl]
    simp only [Function.update_apply, hr12, hr13, hr17, hcl, if_true, if_false,
      show (14 : ℕ) ≠ 12 by omega, show (14 : ℕ) ≠ 13 by omega, show (15 : ℕ) ≠ 14 by omega,
      show (16 : ℕ) ≠ 14 by omega, show (16 : ℕ) ≠ 15 by omega, show (13 : ℕ) ≠ 14 by omega,
      show (12 : ℕ) ≠ 14 by omega, show (15 : ℕ) ≠ 16 by omega, show (13 : ℕ) ≠ 15 by omega]
    have e1 := kappa_bits_le B (a := 6 + st.regs 10 + cl) (M := A) (by omega)
    have e2 := kappa_bits_le B (a := cl + pr) (M := A) (by omega)
    have e3 := kappa_bits_le B (a := cl % pr + cxm) (M := A) (by omega)
    have e4 := kappa_bits_le B (a := cxm + cl % pr) (M := A) (by omega)
    have e5 := kappa_bits_le B (a := cl % pr - cxm + (cxm - cl % pr)) (M := A) (by omega)
    have e6 := kappa_bits_le B (a := 0) (M := A) (by omega)
    split_ifs <;> omega

theorem encStep_spec (st : HS) (good A : ℕ) (hg : good ≤ 1) (h7 : st.regs 7 = good)
    (hA : st.regs 5 + st.regs 2 + st.regs 8 + 2 ≤ A) :
    let st' := encStep.exec inp st
    st'.regs 6 = (if good = 1 ∧ st.regs 5 = st.regs 2 then st.regs 8 else st.regs 6) ∧
    st'.regs 5 = st.regs 5 + good ∧
    (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 15 → r ≠ 16 → st'.regs r = st.regs r) ∧
    st'.mem = st.mem ∧ st'.cur = st.cur ∧ st'.out = st.out ∧
    encStep.cost inp B st ≤ 10 * kappa B (RAM.bits A) := by
  intro st'
  obtain ⟨c, hc5⟩ : ∃ c, st.regs 5 = c := ⟨_, rfl⟩
  obtain ⟨j, hj2⟩ : ∃ j, st.regs 2 = j := ⟨_, rfl⟩
  obtain ⟨i, hi8⟩ : ∃ i, st.regs 8 = i := ⟨_, rfl⟩
  rw [hc5, hj2, hi8] at hA ⊢
  set e := (c - j) + (j - c) + (1 - good) with he
  have hd : e = 0 ↔ (good = 1 ∧ c = j) := by omega
  set s7 := (((((st.setR 15 (c - j)).setR 16 (j - c)).setR 15 ((c - j) + (j - c))).setR 16 1).setR 16
      (1 - good)).setR 15 e with hs7
  have hs7' : (seqs [ar .sub 15 5 2, ar .sub 16 2 5, ar .add 15 15 16, lit 16 1, ar .sub 16 16 7,
      ar .add 15 15 16]).exec inp st = s7 := by
    simp only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_lit, arith_sub, arith_add, HS.setR_regs]
    simp [Function.update_apply, hs7, h7, hc5, hj2, he]
  have h15 : s7.regs 15 = e := by simp [hs7]
  have hr : ∀ r, r ≠ 15 → r ≠ 16 → s7.regs r = st.regs r := by
    intro r h1 h2; simp [hs7, Function.update_apply, h1, h2]
  have hst' : st' = (ar .add 5 5 7).exec inp ((Cmd.ifz 15 (cp 6 8) .skip).exec inp s7) := by
    rw [← hs7']; rfl
  have hif : ∀ r, r ≠ 6 → ((Cmd.ifz 15 (cp 6 8) .skip).exec inp s7).regs r = s7.regs r := by
    intro r h; simp only [exec_ifz]; split_ifs <;> simp [Function.update_apply, h]
  have h6 : ((Cmd.ifz 15 (cp 6 8) .skip).exec inp s7).regs 6 =
      (if good = 1 ∧ c = j then i else st.regs 6) := by
    simp only [exec_ifz, h15]
    by_cases hc : good = 1 ∧ c = j
    · rw [if_pos (hd.mpr hc), if_pos hc]; simp [hr 8 (by omega) (by omega), hi8]
    · rw [if_neg (fun h => hc (hd.mp h)), if_neg hc]; simp [hr 6 (by omega) (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst']; simp only [exec_ar, HS.setR_regs]; rw [Function.update_of_ne (by omega), h6]
  · rw [hst']; simp only [exec_ar, HS.setR_regs, Function.update_self, arith_add]
    rw [hif 5 (by omega), hif 7 (by omega), hr 5 (by omega) (by omega), hr 7 (by omega) (by omega), h7,
      hc5]
  · intro r h1 h2 h3 h4
    rw [hst']; simp only [exec_ar, HS.setR_regs]; rw [Function.update_of_ne h1, hif r h2, hr r h3 h4]
  · rw [hst']; simp only [exec_ar, HS.setR_mem, exec_ifz]; split_ifs <;> simp [hs7]
  · rw [hst']; simp only [exec_ar, HS.setR_cur, exec_ifz]; split_ifs <;> simp [hs7]
  · rw [hst']; simp only [exec_ar, HS.setR_out, exec_ifz]; split_ifs <;> simp [hs7]
  · have hc : encStep.cost inp B st =
        (seqs [ar .sub 15 5 2, ar .sub 16 2 5, ar .add 15 15 16, lit 16 1, ar .sub 16 16 7,
          ar .add 15 15 16]).cost inp B st + ((Cmd.ifz 15 (cp 6 8) .skip).cost inp B s7 +
          ((ar .add 5 5 7).cost inp B ((Cmd.ifz 15 (cp 6 8) .skip).exec inp s7) + 0)) := by
      rw [← hs7']; rfl
    rw [hc]
    have c1 : (seqs [ar .sub 15 5 2, ar .sub 16 2 5, ar .add 15 15 16, lit 16 1, ar .sub 16 16 7,
        ar .add 15 15 16]).cost inp B st ≤ 6 * kappa B (RAM.bits A) := by
      simp only [cost_seqs_cons, cost_seqs_nil, cost_ar, cost_lit, exec_seqs_cons, exec_ar, exec_lit,
        arith_sub, arith_add, HS.setR_regs]
      simp only [Function.update_apply, h7, hc5, hj2, if_true, if_false, show (5 : ℕ) ≠ 15 by omega,
        show (2 : ℕ) ≠ 15 by omega, show (2 : ℕ) ≠ 16 by omega, show (5 : ℕ) ≠ 16 by omega,
        show (15 : ℕ) ≠ 16 by omega, show (16 : ℕ) ≠ 15 by omega, show (7 : ℕ) ≠ 16 by omega,
        show (7 : ℕ) ≠ 15 by omega]
      have e1 := kappa_bits_le B (a := c + j) (M := A) (by omega)
      have e2 := kappa_bits_le B (a := j + c) (M := A) (by omega)
      have e3 := kappa_bits_le B (a := c - j + (j - c)) (M := A) (by omega)
      have e4 := kappa_bits_le B (a := 1) (M := A) (by omega)
      have e5 := kappa_bits_le B (a := 1 + good) (M := A) (by omega)
      have e6 := kappa_bits_le B (a := c - j + (j - c) + (1 - good)) (M := A) (by omega)
      omega
    have c2 : (Cmd.ifz 15 (cp 6 8) .skip).cost inp B s7 ≤ 2 * kappa B (RAM.bits A) := by
      simp only [cost_ifz, cost_cp, cost_skip, h15, hr 8 (by omega) (by omega), hi8]
      have e1 := kappa_bits_le B (a := e) (M := A) (by omega)
      have e2 := kappa_bits_le B (a := i) (M := A) (by omega)
      split_ifs <;> omega
    have c3 : (ar .add 5 5 7).cost inp B ((Cmd.ifz 15 (cp 6 8) .skip).exec inp s7) ≤
        kappa B (RAM.bits A) := by
      simp only [cost_ar]
      rw [hif 5 (by omega), hif 7 (by omega), hr 5 (by omega) (by omega), hr 7 (by omega) (by omega), h7,
        hc5]
      exact kappa_bits_le B (by omega)
    omega

theorem encBody_spec (st : HS) (i pr Cx V X : ℕ) (cl : ℕ → ℕ) (h1 : st.regs 1 = 1)
    (h8 : st.regs 8 = i) (hpr : st.arr 1 i = pr) (h3 : st.regs 3 = Cx) (h4 : st.regs 4 = V)
    (h17 : st.regs 17 = 6) (hcl : ∀ l < V, st.arr 6 l = cl l)
    (hX : Cx ≤ X ∧ V ≤ X ∧ pr ≤ X ∧ i ≤ X ∧ st.regs 5 ≤ X ∧ st.regs 2 ≤ X)
    (hclX : ∀ l < V, cl l ≤ X) :
    let st' := encBody.exec inp st
    let G := (List.range V).all (fun l => decide (Cx % pr ≠ cl l % pr))
    st'.regs 6 = (if G = true ∧ st.regs 5 = st.regs 2 then i else st.regs 6) ∧
    st'.regs 5 = st.regs 5 + (if G = true then 1 else 0) ∧
    (∀ r, (r < 5 ∨ r = 8 ∨ 17 ≤ r) → st'.regs r = st.regs r) ∧
    st'.mem = st.mem ∧ st'.cur = st.cur ∧ st'.out = st.out ∧
    encBody.cost inp B st ≤ (10 * V + 16) * kappa B (RAM.bits (8 * X + 8)) := by
  intro st' G
  obtain ⟨xC, xV, xp, xi, x5, x2⟩ := hX
  set A := 8 * X + 8 with hAd
  set κ := kappa B (RAM.bits A) with hκ
  set f := fun l => decide (Cx % pr ≠ cl l % pr) with hf
  -- prefix
  set sA := ((st.setR 12 pr).setR 13 (Cx % pr)).setR 7 1 with hsA
  have hsA' : (seqs [ald 12 1 8, ar .mod 13 3 12, lit 7 1]).exec inp st = sA := by
    simp only [exec_seqs_cons, exec_seqs_nil, exec_ald, exec_ar, exec_lit, arith_mod, HS.setR_regs,
      h1, h8, hpr]
    simp [hsA, Function.update_apply, h3]
  have rA : ∀ r, r ≠ 7 → r ≠ 12 → r ≠ 13 → sA.regs r = st.regs r := by
    intro r a b c; simp [hsA, Function.update_apply, a, b, c]
  have cA : (seqs [ald 12 1 8, ar .mod 13 3 12, lit 7 1]).cost inp B st ≤ 3 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_ald, cost_ar, cost_lit, exec_seqs_cons, exec_ald,
      exec_ar, HS.setR_regs, HS.setR_arr, h1, h8, hpr]
    simp only [Function.update_apply, show (3 : ℕ) ≠ 12 by omega, if_false, if_true, h3]
    have e1 := kappa_bits_le B (a := 1 + i + pr) (M := A) (by omega)
    have e2 := kappa_bits_le B (a := Cx + pr) (M := A) (by omega)
    have e3 := kappa_bits_le B (a := 1) (M := A) (by omega)
    omega
  have sA4 : sA.regs 4 = V := by rw [rA 4 (by omega) (by omega) (by omega), h4]
  -- inner loop
  have IN := forLoop_spec inp B 10 4 11 encInner sA (by omega) (by omega)
    (fun k s' => s'.regs 7 = (if (List.range k).all f = true then 1 else 0) ∧
      (∀ r, r ≠ 7 → r ≠ 10 → r ≠ 11 → r ≠ 14 → r ≠ 15 → r ≠ 16 → s'.regs r = sA.regs r) ∧
      s'.mem = st.mem ∧ s'.cur = st.cur ∧ s'.out = st.out)
    (fun _ => 7 * κ)
    ⟨by simp [hsA], fun r a b _ _ _ _ => by simp [Function.update_apply, b], by simp [hsA],
      by simp [hsA], by simp [hsA]⟩
    (by
      intro k hk s' ⟨g7, gr, gm, gc, go⟩ g10
      rw [sA4] at hk
      have e17 : s'.regs 17 = 6 := by
        rw [gr 17 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          rA 17 (by omega) (by omega) (by omega), h17]
      have e12 : s'.regs 12 = pr := by
        rw [gr 12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; simp [hsA]
      have e13 : s'.regs 13 = Cx % pr := by
        rw [gr 13 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; simp [hsA]
      have ecl : s'.arr 6 (s'.regs 10) = cl k := by
        rw [g10]; simp only [HS.arr, gm]; exact hcl k hk
      have hclk := hclX k hk
      have hmod : Cx % pr ≤ Cx := Nat.mod_le _ _
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := encInner_spec inp B s' (cl k) pr (Cx % pr) A e17 e12 e13 ecl
        (by rw [g10]; omega)
      refine ⟨by rw [i2 10 (by omega) (by omega) (by omega) (by omega), g10], ⟨?_, ?_, ?_, ?_, ?_⟩, i6⟩
      · simp only [HS.setR_regs]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), i1, g7,
          List.range_succ, List.all_append]
        simp only [List.all_cons, List.all_nil, Bool.and_true, hf]
        by_cases hc : cl k % pr = Cx % pr
        · rw [if_pos hc]; simp [hc]
        · rw [if_neg hc]
          have : decide (Cx % pr ≠ cl k % pr) = true := by simp; omega
          rw [this, Bool.and_true]
      · intro r a b c d e g
        simp only [HS.setR_regs]
        rw [Function.update_of_ne b, Function.update_of_ne c, i2 r a d e g]
        exact gr r a b c d e g
      · simp [i3, gm]
      · simp [i4, gc]
      · simp [i5, go])
  rw [sA4] at IN
  obtain ⟨⟨n7, nr, nm, nc, no⟩, ncost⟩ := IN
  set sB := (forLoop 10 4 11 encInner).exec inp sA with hsB
  have g01 : (if (List.range V).all f = true then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have sB5 : sB.regs 5 = st.regs 5 := by
    rw [nr 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      rA 5 (by omega) (by omega) (by omega)]
  have sB2 : sB.regs 2 = st.regs 2 := by
    rw [nr 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      rA 2 (by omega) (by omega) (by omega)]
  have sB8 : sB.regs 8 = i := by
    rw [nr 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      rA 8 (by omega) (by omega) (by omega), h8]
  have sB6 : sB.regs 6 = st.regs 6 := by
    rw [nr 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      rA 6 (by omega) (by omega) (by omega)]
  obtain ⟨t6, t5, tr, tm, tc, tou, tcost⟩ := encStep_spec inp B sB _ A g01 n7 (by omega)
  have hex : st' = encStep.exec inp sB := by
    show encStep.exec inp ((forLoop 10 4 11 encInner).exec inp
      ((seqs [ald 12 1 8, ar .mod 13 3 12, lit 7 1]).exec inp st)) = _
    rw [hsA']
  have hGf : G = (List.range V).all f := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hex, t6, sB5, sB2, sB8, sB6, hGf]
    by_cases hG : (List.range V).all f = true
    · simp [hG]
    · simp [hG]
  · rw [hex, t5, sB5, hGf]
  · intro r hr
    rw [hex, tr r (by omega) (by omega) (by omega) (by omega),
      nr r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      rA r (by omega) (by omega) (by omega)]
  · rw [hex, tm, nm]
  · rw [hex, tc, nc]
  · rw [hex, tou, no]
  · have hc : encBody.cost inp B st = (seqs [ald 12 1 8, ar .mod 13 3 12, lit 7 1]).cost inp B st +
        ((forLoop 10 4 11 encInner).cost inp B ((seqs [ald 12 1 8, ar .mod 13 3 12, lit 7 1]).exec inp st) +
          (encStep.cost inp B ((forLoop 10 4 11 encInner).exec inp
            ((seqs [ald 12 1 8, ar .mod 13 3 12, lit 7 1]).exec inp st)) + 0)) := rfl
    rw [hsA', ← hsB] at hc
    rw [← hκ] at tcost
    rw [hc]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at ncost
    have eV := kappa_bits_le B (a := V) (M := A) (by omega)
    have : (10 * V + 16) * κ = 3 * κ + (3 * (V + 1) * κ + V * (7 * κ)) + 10 * κ := by ring
    rw [this]
    have : 3 * (V + 1) * kappa B (RAM.bits V) ≤ 3 * (V + 1) * κ := Nat.mul_le_mul_left _ eV
    omega

/-- **Phase D.** -/
theorem encD_spec_oai (q t n p : ℕ) (s : HS) (hs : EBase q t n p s) (cl : ℕ → ℕ) (X : ℕ)
    (hcl : ∀ l < s.regs 4, s.arr 6 l = cl l) (hclX : ∀ l < s.regs 4, cl l ≤ X)
    (h3 : s.regs 3 ≤ X) (h4 : s.regs 4 ≤ X) (h2 : s.regs 2 ≤ X) (hL : (parameters q t n).L ≤ X)
    (hpb : primeBound (parameters q t n).L ≤ X) :
    let s' := encD.exec inp s
    EBase q t n p s' ∧
    s'.regs 6 = (((List.range (parameters q t n).L).filter
      (goodTest (s.regs 3) (s.regs 4) cl))[s.regs 2]?).getD (parameters q t n).L ∧
    s'.regs 2 = s.regs 2 ∧ s'.regs 3 = s.regs 3 ∧ s'.mem = s.mem ∧ s'.cur = s.cur ∧ s'.out = s.out ∧
    encD.cost inp B s ≤ (3 * ((parameters q t n).L + 1) + (parameters q t n).L * (10 * s.regs 4 + 16) + 3) *
      kappa B (RAM.bits (8 * X + 8)) := by
  intro s'
  set P := parameters q t n with hP
  set A := 8 * X + 8 with hAd
  set κ := kappa B (RAM.bits A) with hκ
  set G := goodTest (s.regs 3) (s.regs 4) cl with hG
  set j := s.regs 2 with hj
  set V := s.regs 4 with hV
  set Cx := s.regs 3 with hCx
  have pL : s.regs 105 = P.L := hs.par.hL
  set s0 := (seqs [lit 5 0, cp 6 105, lit 17 6]).exec inp s with hs0
  have r0 : ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 17 → s0.regs r = s.regs r := by
    intro r a b c; simp [hs0, Function.update_apply, a, b, c]
  have c0 : (seqs [lit 5 0, cp 6 105, lit 17 6]).cost inp B s ≤ 3 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons, exec_lit, HS.setR_regs]
    simp only [Function.update_apply, show (105 : ℕ) ≠ 5 by omega, if_false, pL]
    have e1 := kappa_bits_le B (a := 0) (M := A) (by omega)
    have e2 := kappa_bits_le B (a := P.L) (M := A) (by omega)
    have e3 := kappa_bits_le B (a := 6) (M := A) (by omega)
    omega
  have s0L : s0.regs 105 = P.L := by rw [r0 105 (by omega) (by omega) (by omega), pL]
  have OUT := forLoop_spec inp B 8 105 9 encBody s0 (by omega) (by omega)
    (fun k st => st.regs 5 = ((List.range k).filter G).length ∧
      st.regs 6 = (((List.range k).filter G)[j]?).getD P.L ∧
      (∀ r, (r < 5 ∨ 17 ≤ r) → st.regs r = s0.regs r) ∧
      st.mem = s.mem ∧ st.cur = s.cur ∧ st.out = s.out)
    (fun _ => (10 * V + 16) * κ)
    ⟨by simp [hs0], by simp [hs0, pL], fun r hr => by simp [Function.update_apply]; omega,
      by simp [hs0], by simp [hs0], by simp [hs0]⟩
    (by
      intro k hk st ⟨g5, g6, gr, gm, gc, go⟩ g8
      rw [s0L] at hk
      have e1 : st.regs 1 = 1 := by rw [gr 1 (by omega), r0 1 (by omega) (by omega) (by omega), hs.r1]
      have epr : st.arr 1 k = primeAt k := by simp only [HS.arr, gm]; exact hs.pr k hk.le
      have e3 : st.regs 3 = Cx := by rw [gr 3 (by omega), r0 3 (by omega) (by omega) (by omega)]
      have e4 : st.regs 4 = V := by rw [gr 4 (by omega), r0 4 (by omega) (by omega) (by omega)]
      have e17 : st.regs 17 = 6 := by rw [gr 17 (by omega)]; simp [hs0]
      have e2 : st.regs 2 = j := by rw [gr 2 (by omega), r0 2 (by omega) (by omega) (by omega)]
      have ecl : ∀ l < V, st.arr 6 l = cl l := fun l hl => by simp only [HS.arr, gm]; exact hcl l hl
      have hc5 : ((List.range k).filter G).length ≤ k := by
        have := List.length_filter_le G (List.range k); simpa using this
      have hpk : primeAt k ≤ X := by
        have := primeAt_lt_primeBound (L := P.L) (i := k) hk.le; omega
      obtain ⟨b6, b5, br, bm, bc, bo, bcost⟩ := encBody_spec inp B st k (primeAt k) Cx V X cl e1 g8 epr
        e3 e4 e17 ecl ⟨h3, h4, hpk, by omega, by omega, by omega⟩ (fun l hl => hclX l hl)
      have hGk : G k = (List.range V).all (fun l => decide (Cx % primeAt k ≠ cl l % primeAt k)) := rfl
      refine ⟨by rw [br 8 (by omega), g8], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, bcost⟩
      · simp only [HS.setR_regs]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), b5, g5,
          filter_range_length_succ, hGk]
      · simp only [HS.setR_regs]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), b6, g6, g5, e2,
          filter_range_getD_succ, hGk]
      · intro r hr
        simp only [HS.setR_regs]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), br r (by omega), gr r hr]
      · simp [bm, gm]
      · simp [bc, gc]
      · simp [bo, go])
  rw [s0L] at OUT
  obtain ⟨⟨o5, o6, or, om, oc, oo⟩, ocost⟩ := OUT
  have hex : s' = (forLoop 8 105 9 encBody).exec inp s0 := rfl
  rw [← hex] at o5 o6 or om oc oo
  refine ⟨hs.congr' (fun r h1 h2 => by rw [or r (by omega), r0 r (by omega) (by omega) (by omega)])
      (by rw [or 1 (by omega), r0 1 (by omega) (by omega) (by omega)])
      (fun i => by simp only [HS.arr, om]), o6, ?_, ?_, om, oc, oo, ?_⟩
  · rw [or 2 (by omega), r0 2 (by omega) (by omega) (by omega)]
  · rw [or 3 (by omega), r0 3 (by omega) (by omega) (by omega)]
  · have hc : encD.cost inp B s = (seqs [lit 5 0, cp 6 105, lit 17 6]).cost inp B s +
        ((forLoop 8 105 9 encBody).cost inp B s0 + 0) := rfl
    rw [hc]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at ocost
    have eL := kappa_bits_le B (a := P.L) (M := A) (by omega)
    have : 3 * (P.L + 1) * kappa B (RAM.bits P.L) ≤ 3 * (P.L + 1) * κ := Nat.mul_le_mul_left _ eL
    have : (3 * (P.L + 1) + P.L * (10 * V + 16) + 3) * κ =
        3 * (P.L + 1) * κ + P.L * ((10 * V + 16) * κ) + 3 * κ := by ring
    rw [this]
    omega

end PhaseD

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.encD_spec_oai := @EditMulticoloring.Dev.Ram.encD_spec_oai
