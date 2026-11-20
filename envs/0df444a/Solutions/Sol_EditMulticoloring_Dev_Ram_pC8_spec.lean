-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.pC8_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:04.113566+00:00
-- url     : https://prove2.me/submissions/cf16e8e0-47e0-4d08-91c0-0ec06d4abeb0

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_word
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne

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
-- module Solutions.EditMulticoloring.RamDecode
/-!
# The decoder, part 1: good-index test, good-index count, writing `repr` (q379, Part D)

* `goodW r piR cxR vR CL`: `regs r := 1` iff `cx % pi ≠ CL[ℓ] % pi` for all `ℓ < V`
  (`pi = regs piR`, `cx = regs cxR`, `V = regs vR`); writes only `r .. r+7`.
* `countW r iR prR piR cxR vR CL`: `regs r := #{i' < regs iR : goodW-test with pi = PR[i']}`;
  writes only `r .. r+3`, `piR`, and the `goodW` block `r+4 .. r+11`.
* `reprOut r vR wR offR X qR`: writes `repr q w v` into array `X` at offset `off`;
  writes only `r .. r+6`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Dec1
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## The good-index test -/

/-! ## Counting the good indices below `i` -/

/-! ## Writing `repr q w v` into an array -/

theorem dec_repr_eq_map {q : ℕ} (hq : 0 < q) (w N : ℕ) :
    Code.repr q w N = (List.range w).map (fun i => (⟨(N / q ^ (w - 1 - i)) % q, Nat.mod_lt _ hq⟩ : Fin q)) := by
  unfold Code.repr
  rw [← List.filterMap_eq_map]
  congr 1; funext i
  simp [Nat.mod_lt _ hq]

theorem dec_repr_length {q : ℕ} (hq : 0 < q) (w N : ℕ) : (Code.repr q w N).length = w := by
  rw [dec_repr_eq_map hq]; simp

theorem dec_repr_getElem {q : ℕ} (hq : 0 < q) (w N i : ℕ) (hi : i < (Code.repr q w N).length) :
    ((Code.repr q w N)[i]).val = (N / q ^ (w - 1 - i)) % q := by
  simp [dec_repr_eq_map hq]

theorem reprOut_spec (r vR wR offR X qR : ℕ) (s : HS) (M : ℕ)
    (hv : vR < r ∨ r + 7 ≤ vR) (hw : wR < r ∨ r + 7 ≤ wR) (ho : offR < r ∨ r + 7 ≤ offR)
    (hqr : qR < r ∨ r + 7 ≤ qR)
    (hM : s.regs vR + s.regs offR + s.regs wR + X + s.regs qR + 1 ≤ M) :
    (∀ i < s.regs wR, ((reprOut r vR wR offR X qR).exec inp s).arr X (s.regs offR + i) =
      (s.regs vR / s.regs qR ^ (s.regs wR - 1 - i)) % s.regs qR) ∧
    (∀ y i, ¬ (y = X ∧ s.regs offR ≤ i ∧ i < s.regs offR + s.regs wR) →
      ((reprOut r vR wR offR X qR).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < r ∨ r + 7 ≤ r') → ((reprOut r vR wR offR X qR).exec inp s).regs r' = s.regs r') ∧
    ((reprOut r vR wR offR X qR).exec inp s).cur = s.cur ∧
    ((reprOut r vR wR offR X qR).exec inp s).out = s.out ∧
    (reprOut r vR wR offR X qR).cost inp B s ≤ (7 * s.regs wR + 7) * kappa B (RAM.bits M) := by
  set v := s.regs vR
  set w := s.regs wR
  set off := s.regs offR
  set q := s.regs qR
  set s1 := (seqs [cp r vR, ar .add (r + 1) offR wR, lit (r + 2) X, lit (r + 3) 1]).exec inp s with hs1
  have r1 : ∀ r', (r' < r ∨ r + 7 ≤ r') → s1.regs r' = s.regs r' := by
    intro r' h; simp (disch := omega) [hs1, upd_ne]
  have v0 : s1.regs r = v := by simp (disch := omega) [hs1, upd_ne, v]
  have v1 : s1.regs (r + 1) = off + w := by simp (disch := omega) [hs1, upd_ne, off, w]
  have v2 : s1.regs (r + 2) = X := by simp (disch := omega) [hs1, upd_ne]
  have v3 : s1.regs (r + 3) = 1 := by simp (disch := omega) [hs1, upd_ne]
  have m1 : s1.mem = s.mem := by simp [hs1]
  have hn1 : s1.regs wR = w := r1 _ hw
  have c1 : (seqs [cp r vR, ar .add (r + 1) offR wR, lit (r + 2) X, lit (r + 3) 1]).cost inp B s ≤
      4 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, cost_cp,
      exec_seqs_cons, exec_lit, exec_cp, exec_ar, HS.setR_regs, upd_ne]
    have := kappa_bits_le B (a := s.regs vR) (M := M) (by omega)
    have := kappa_bits_le B (a := s.regs offR + s.regs wR) (M := M) (by omega)
    have := kappa_bits_le B (a := X) (M := M) (by omega)
    have := kappa_bits_le B (a := 1) (M := M) (by omega)
    omega
  have K := forLoop_spec inp B (r + 4) wR (r + 5) (reprBody r qR) s1
    (by omega) (by omega)
    (fun k st => st.regs r = v / q ^ k ∧ st.regs (r + 1) = off + w - k ∧ st.regs (r + 2) = X ∧
      st.regs (r + 3) = 1 ∧
      (∀ i, off + w - k ≤ i → i < off + w → st.arr X i = (v / q ^ (off + w - 1 - i)) % q) ∧
      (∀ y i, ¬ (y = X ∧ off + w - k ≤ i ∧ i < off + w) → st.arr y i = s.arr y i) ∧
      (∀ r', (r' < r ∨ r + 7 ≤ r') → st.regs r' = s.regs r') ∧ st.cur = s.cur ∧ st.out = s.out)
    (fun _ => 4 * kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [upd_ne, v0], by simp (disch := omega) [upd_ne, v1],
      by simp (disch := omega) [upd_ne, v2], by simp (disch := omega) [upd_ne, v3],
      fun i h1 h2 => by omega, fun y i _ => by simp [HS.arr, m1],
      fun r' h => by simp (disch := omega) [upd_ne, r1 r' h], by simp [hs1], by simp [hs1]⟩
    (by
      intro k hk st ⟨h0, h1, h2, h3, hc, hy, hr, hcur, hout⟩ hj
      rw [hn1] at hk
      have eq : st.regs qR = q := hr _ hqr
      have hle : v / q ^ k ≤ v := Nat.div_le_self _ _
      have hmod : v / q ^ k % q ≤ v / q ^ k := Nat.mod_le _ _
      have e1 := kappa_bits_le B (a := off + w - k + 1) (M := M) (by omega)
      have e2 := kappa_bits_le B (a := v / q ^ k + q) (M := M) (by omega)
      have e3 := kappa_bits_le B (a := X + (off + w - k - 1) + v / q ^ k % q) (M := M) (by omega)
      simp only [reprBody, exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ast, cost_seqs_cons,
        cost_seqs_nil, cost_ar, cost_ast, HS.setR_regs, HS.store_regs, HS.setR_cur,
        HS.store_cur, HS.setR_out, HS.store_out, HS.setR_arr, arith_sub, arith_mod, arith_div]
      refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hcur, hout⟩, ?_⟩
      · simp (disch := omega) only [upd_ne, upd_eq, h0, eq]
        rw [Nat.div_div_eq_div_mul, pow_succ]
      · simp (disch := omega) only [upd_ne, upd_eq, h1, h3]; omega
      · simp (disch := omega) only [upd_ne, upd_eq]; exact h2
      · simp (disch := omega) only [upd_ne, upd_eq]; exact h3
      · intro i hi1 hi2
        simp (disch := omega) only [upd_ne, upd_eq, HS.store_arr, h0, h1, h2, h3, eq]
        split_ifs with hik
        · have : off + w - 1 - i = k := by omega
          rw [this]
        · simp only [true_and] at hik
          simp only [HS.setR_arr]; exact hc i (by omega) hi2
      · intro y i hyi
        simp (disch := omega) only [upd_ne, upd_eq, HS.store_arr, h0, h1, h2, h3, eq]
        split_ifs with hik
        · exfalso; apply hyi; omega
        · simp only [HS.setR_arr]; exact hy y i (by omega)
      · intro r' h
        simp (disch := omega) only [upd_ne]; exact hr r' h
      · simp (disch := omega) only [upd_ne, upd_eq, h0, h1, h2, h3, eq, hj]
        have e4 := kappa_bits_le B (a := off + w - k - 1 + 1) (M := M) (by omega)
        omega)
  rw [hn1] at K
  obtain ⟨⟨-, -, -, -, k2, k3, k4, k5, k6⟩, k7⟩ := K
  have hex : (reprOut r vR wR offR X qR).exec inp s =
      (forLoop (r + 4) wR (r + 5) (reprBody r qR)).exec inp s1 := rfl
  rw [hex]
  refine ⟨fun i hi => ?_, fun y i h => k3 y i (by omega), k4, k5, k6, ?_⟩
  · rw [k2 _ (by omega) (by omega)]
    have : off + w - 1 - (off + i) = w - 1 - i := by omega
    rw [this]
  · have hc : (reprOut r vR wR offR X qR).cost inp B s =
        (seqs [cp r vR, ar .add (r + 1) offR wR, lit (r + 2) X, lit (r + 3) 1]).cost inp B s +
        (forLoop (r + 4) wR (r + 5) (reprBody r qR)).cost inp B s1 := rfl
    rw [hc]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k7
    have := kappa_bits_le B (a := w) (M := M) (by omega)
    nlinarith

theorem reprOut_word {q : ℕ} (hq : 0 < q) (r vR wR offR X qR : ℕ) (s : HS)
    (hv : vR < r ∨ r + 7 ≤ vR) (hw : wR < r ∨ r + 7 ≤ wR) (ho : offR < r ∨ r + 7 ≤ offR)
    (hqr : qR < r ∨ r + 7 ≤ qR) (hqv : s.regs qR = q) :
    WordAt ((reprOut r vR wR offR X qR).exec inp s) X (s.regs offR)
      (Code.repr q (s.regs wR) (s.regs vR)) := by
  have := (reprOut_spec inp 0 r vR wR offR X qR s _ hv hw ho hqr le_rfl).1
  intro i hi
  rw [dec_repr_length hq] at hi
  rw [this i hi, dec_repr_getElem hq, hqv]

end Dec1

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

theorem WordAt.appendD {q : ℕ} {s : HS} {X : ℕ} {x y : Word q} (hx : WordAt s X 0 x)
    (hy : WordAt s X x.length y) : WordAt s X 0 (x ++ y) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases h : i < x.length
  · rw [List.getElem_append_left h]; exact hx i h
  · rw [List.getElem_append_right (by omega)]
    have := hy (i - x.length) (by omega)
    rw [show x.length + (i - x.length) = i by omega] at this
    rw [zero_add, this]

theorem WordAt.takeD {q : ℕ} {s : HS} {X : ℕ} {w : Word q} (hw : WordAt s X 0 w) (m : ℕ) :
    WordAt s X 0 (w.take m) := by
  intro i hi
  rw [List.length_take] at hi
  rw [List.getElem_take]; exact hw i (by omega)

/-! ## Layout -/

/-! ## Size bounds -/

theorem dec_m_le_k (q t n : ℕ) : (parameters q t n).m ≤ (parameters q t n).k := by
  show (parameters q t n).m ≤ (parameters q t n).m + floorLog q (parameters q t n).J
  omega

section Levels
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Level 8: store the result `x ++ repr q (k - m) j` and set the done flag -/

theorem pC8_spec_oai {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (j : ℕ) (hj : st.regs 240 = j) (hjL : j ≤ (parameters q t n).L) :
    DOut t st ((pC8 t).exec inp st)
      (some (w.take (parameters q t n).m ++
        Code.repr q ((parameters q t n).k - (parameters q t n).m) j)) ∧
    (pC8 t).cost inp B st ≤ (7 * n + 7 * (parameters q t n).k + 30) * kappa B (RAM.bits (DM q t n)) := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hmk : P.m ≤ P.k := dec_m_le_k q t n
  have hmn : P.m ≤ n := params_m_le q t n
  have hm115 : st.regs 115 = P.m := hc.par.hm
  have hk116 : st.regs 116 = P.k := hc.par.hk
  have ha0 : (dC0 t).a0 = 14 + 4 * t := rfl
  set x := w.take P.m with hx
  have hxl : x.length = P.m := by rw [hx, List.length_take]; omega
  -- block 1
  set A1 := seqs [lit 220 (dC0 t).a0, lit 221 0, lit 222 2, lit 223 0, cp 224 115] with hA1
  set s1 := A1.exec inp st with hs1
  have r1 : ∀ r, (r < 220 ∨ 225 ≤ r) → s1.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs1, hA1, upd_ne]
  have m1 : s1.mem = st.mem := by simp [hs1, hA1]
  have v220 : s1.regs 220 = 14 + 4 * t := by simp (disch := omega) [hs1, hA1, upd_ne, ha0]
  have v221 : s1.regs 221 = 0 := by simp (disch := omega) [hs1, hA1, upd_ne]
  have v222 : s1.regs 222 = 2 := by simp (disch := omega) [hs1, hA1, upd_ne]
  have v223 : s1.regs 223 = 0 := by simp (disch := omega) [hs1, hA1, upd_ne]
  have v224 : s1.regs 224 = P.m := by simp (disch := omega) [hs1, hA1, upd_ne, hm115]
  have c1 : A1.cost inp B st ≤ 5 * κ := by
    simp (disch := omega) only [hA1, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, hm115, ha0]
    have := kb (14 + 4 * t) (by omega)
    have := kb 0 (by omega)
    have := kb 2 (by omega)
    have := kb P.m (by omega)
    omega
  have hw1 : WordAt s1 (14 + 4 * t) 0 x := by
    rw [← ha0]; exact (hw.takeD P.m).congr (fun i _ => by simp [HS.arr, m1])
  -- copy x to the result array
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
  -- k - m
  set s3 := s2.setR 253 (s2.regs 116 - s2.regs 115) with hs3
  have v253 : s3.regs 253 = P.k - P.m := by
    simp [hs3, r2 116 (by omega), r2 115 (by omega), hk116, hm115]
  have r3 : ∀ r, r ≠ 253 → s3.regs r = s2.regs r := by
    intro r hr; simp [hs3, upd_ne hr]
  have c3 : (ar .sub 253 116 115).cost inp B s2 ≤ κ := by
    simp only [cost_ar]; rw [r2 116 (by omega), r2 115 (by omega), hk116, hm115]
    exact kb _ (by omega)
  -- repr
  have e240 : s3.regs 240 = j := by rw [r3 _ (by omega), r2 _ (by omega), hj]
  have e115 : s3.regs 115 = P.m := by rw [r3 _ (by omega), r2 _ (by omega), hm115]
  have e4 : s3.regs 4 = q := by rw [r3 _ (by omega), r2 _ (by omega), hc.q4]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := reprOut_spec inp B 255 240 253 115 2 4 s3 (DM q t n)
    (by omega) (by omega) (by omega) (by omega)
    (by rw [e240, v253, e115, e4]; omega)
  have hr4 := reprOut_word inp (q := q) (by omega) 255 240 253 115 2 4 s3
    (by omega) (by omega) (by omega) (by omega) e4
  rw [e240, v253, e115] at hr4
  rw [e115, v253] at d2
  rw [v253] at d6
  set s4 := (reprOut 255 240 253 115 2 4).exec inp s3 with hs4
  set s5 := s4.setR 2 1 with hs5
  have hex : (pC8 t).exec inp st = s5 := rfl
  have hco : (pC8 t).cost inp B st = A1.cost inp B st +
      ((copyW 220 221 222 223 224 225 226 227 228).cost inp B s1 +
      ((ar .sub 253 116 115).cost inp B s2 + ((reprOut 255 240 253 115 2 4).cost inp B s3 +
      ((lit 2 1).cost inp B s4 + 0)))) := rfl
  have hfr4 : ∀ r, (r < 220 ∨ 262 ≤ r) → s4.regs r = st.regs r := by
    intro r hr
    rw [d3 r (by omega), r3 r (by omega), r2 r (by omega)]
  have harr4 : ∀ y i, y ≠ 2 → s4.arr y i = st.arr y i := by
    intro y i hy
    rw [d2 y i (by omega), show s3.arr y i = s2.arr y i from rfl, b2 y i (by omega)]
    simp [HS.arr, m1]
  rw [hex]
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨fun h => by simp at h, ?_⟩⟩, ?_⟩
  · intro r hr
    unfold KeptR at hr
    simp only [hs5, HS.setR_regs]
    rw [upd_ne (by omega), hfr4 r (by omega)]
  · intro y i hy
    unfold KeptA at hy
    simp only [hs5, HS.setR_arr]
    exact harr4 y i (by omega)
  · simp only [hs5, HS.setR_cur, d4, hs3, HS.setR_cur, b4, hs1, hA1]; simp
  · simp only [hs5, HS.setR_out, d5, hs3, HS.setR_out, b5, hs1, hA1]; simp
  · intro r hr
    simp only [Option.some.injEq] at hr
    subst hr
    refine ⟨by simp [hs5], ?_⟩
    apply WordAt.appendD
    · intro i hi
      simp only [hs5, HS.setR_arr]
      rw [zero_add, d2 2 i (by rw [hxl] at hi; omega), show s3.arr 2 i = s2.arr 2 i from rfl]
      have := hx2 i hi; rwa [zero_add] at this
    · intro i hi
      simp only [hs5, HS.setR_arr]
      rw [hxl]; exact hr4 i hi
  · rw [hco]
    have c5 : (lit 2 1).cost inp B s4 ≤ κ := by simp only [cost_lit]; exact kb 1 (by omega)
    have c2 : (copyW 220 221 222 223 224 225 226 227 228).cost inp B s1 ≤ (7 * P.m + 3) * κ := b6
    have hkm : P.k - P.m ≤ P.k := Nat.sub_le _ _
    have h1 : (7 * P.m + 3) * κ ≤ (7 * n + 3) * κ := Nat.mul_le_mul_right _ (by omega)
    have h2 : (7 * (P.k - P.m) + 7) * κ ≤ (7 * P.k + 7) * κ := Nat.mul_le_mul_right _ (by omega)
    have h3 : (7 * n + 7 * P.k + 30) * κ = 5 * κ + (7 * n + 3) * κ + κ + (7 * P.k + 7) * κ + κ + 13 * κ := by
      ring
    rw [h3]
    have := c1
    linarith

/-! ## Level 7: count the good indices below `i`, compare with `J`, store -/

/-! ## Level 6: compare `η` with the colour of `x` modulo `primeAt i` -/

/-! ## Level 5: the colours (`colorsAll`), the test `localGood x i` -/

/-! ## Level 4: `pi := PR[i]`, test `η < pi` -/

/-! ## Level 3: `i := idx / q^h₂`, `η := idx % q^h₂`, test `i < L` -/

/-! ## Level 2: `idx := INV - 1`, test `idx < q^h` -/

/-! ## The candidate test: value of the tail, `INV` lookup -/

end Levels

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.pC8_spec_oai := @EditMulticoloring.Dev.Ram.pC8_spec_oai
