-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.encB_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:36:36.328942+00:00
-- url     : https://prove2.me/submissions/f9390605-681c-42c5-9f49-92e702e4ad6b

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_word
import Theorems.Thm_EditMulticoloring_Dev_Ram_inputAt_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_inputAt_sub_one
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_readW_spec
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

section Frames
variable (inp : ℕ → ℕ)

theorem iterate_induct {f : HS → HS} (P : HS → Prop) (h : ∀ s, P s → P (f s)) :
    ∀ (n : ℕ) (s : HS), P s → P (f^[n] s)
  | 0, _, hs => hs
  | n + 1, s, hs => by rw [Function.iterate_succ_apply]; exact iterate_induct P h n _ (h _ hs)

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

end Frames

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

theorem horner_lt (q : ℕ) (g : ℕ → ℕ) (N : ℕ) (hg : ∀ i < N, g i < q) :
    ∀ k ≤ N, horner q g k < q ^ k := by
  intro k hk
  induction k with
  | zero => simp [horner]
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := hg k (by omega)
    simp only [horner, pow_succ]
    have : horner q g k + 1 ≤ q ^ k := h1
    nlinarith

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

theorem valueW_spec (r : ℕ) (s : HS) (M : ℕ)
    (hcell : ∀ i < s.regs (r + 2), s.arr (s.regs r) (s.regs (r + 1) + i) < s.regs (r + 3))
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + s.regs (r + 3) +
      s.regs (r + 3) ^ s.regs (r + 2) ≤ M) :
    ((valueW r).exec inp s).regs (r + 4) =
      horner (s.regs (r + 3)) (fun i => s.arr (s.regs r) (s.regs (r + 1) + i)) (s.regs (r + 2)) ∧
    (∀ r', (r' < r + 4 ∨ r + 9 ≤ r') → ((valueW r).exec inp s).regs r' = s.regs r') ∧
    ((valueW r).exec inp s).mem = s.mem ∧
    ((valueW r).exec inp s).cur = s.cur ∧
    ((valueW r).exec inp s).out = s.out ∧
    (valueW r).cost inp B s ≤ (7 * s.regs (r + 2) + 4) * kappa B (RAM.bits M) := by
  set vX := s.regs r
  set voff := s.regs (r + 1)
  set q := s.regs (r + 3)
  set g := fun i => s.arr vX (voff + i) with hg
  set s1 := s.setR (r + 4) 0 with hs1
  have hn1 : s1.regs (r + 2) = s.regs (r + 2) := by simp [hs1]
  have hlt := horner_lt q g (s.regs (r + 2)) hcell
  have K := forLoop_spec inp B (r + 5) (r + 2) (r + 8) (seqs [ar .add (r + 6) (r + 1) (r + 5),
    ald (r + 7) r (r + 6), ar .mul (r + 4) (r + 3) (r + 4), ar .add (r + 4) (r + 4) (r + 7)]) s1
    (by omega) (by omega)
    (fun k st => st.regs (r + 4) = horner q g k ∧
      (∀ r', (r' < r + 4 ∨ r + 9 ≤ r') → st.regs r' = s.regs r') ∧ st.mem = s.mem)
    (fun _ => 4 * kappa B (RAM.bits M))
    ⟨by simp [hs1, horner], fun r' h => by simp (disch := omega) [hs1, upd_ne], by simp [hs1]⟩
    (by
      intro k hk st ⟨hv, hr, hm⟩ hj
      rw [hn1] at hk
      have eX : st.regs r = vX := hr r (by omega)
      have eoff : st.regs (r + 1) = voff := hr _ (by omega)
      have eq : st.regs (r + 3) = q := hr _ (by omega)
      have hA : st.arr vX (voff + k) = g k := by simp [HS.arr, hm, hg]
      have hgk := hcell k hk
      have hq1 : 1 ≤ q := by omega
      have hpow : q ^ (k + 1) ≤ q ^ s.regs (r + 2) := Nat.pow_le_pow_right hq1 (by omega)
      have hpk : q ^ k ≤ q ^ s.regs (r + 2) := Nat.pow_le_pow_right hq1 (by omega)
      have hk1 := hlt (k + 1) (by omega)
      have hk0 := hlt k (by omega)
      simp only [horner] at hk1
      simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ald,
        arith_add, arith_mul, HS.setR_regs, HS.setR_arr, HS.setR_mem,
        upd_ne, upd_eq, eX, eoff, eq, hj, hA, hv, cost_seqs_cons, cost_seqs_nil, cost_ar,
        cost_ald]
      refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_⟩, ?_⟩
      · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, horner]
      · intro r' h
        simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
      · simpa using hm
      · have e1 := kappa_bits_le B (a := voff + k) (M := M) (by omega)
        have e2 := kappa_bits_le B (a := vX + (voff + k) + g k) (M := M) (by omega)
        have e3 := kappa_bits_le B (a := q + horner q g k) (M := M) (by omega)
        have e4 := kappa_bits_le B (a := q * horner q g k + g k) (M := M) (by omega)
        omega)
  rw [hn1] at K
  obtain ⟨⟨k1, k2, k3⟩, k4⟩ := K
  have hcur : ((valueW r).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((valueW r).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  refine ⟨k1, k2, k3, hcur, hout, ?_⟩
  have hc : (valueW r).cost inp B s = kappa B (RAM.bits 0) +
      (forLoop (r + 5) (r + 2) (r + 8) (seqs [ar .add (r + 6) (r + 1) (r + 5),
    ald (r + 7) r (r + 6), ar .mul (r + 4) (r + 3) (r + 4), ar .add (r + 4) (r + 4) (r + 7)])).cost
      inp B s1 := rfl
  rw [hc]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
  have := kappa_bits_le B (a := s.regs (r + 2)) (M := M) (by omega)
  have := kappa_bits_le B (a := 0) (M := M) (by omega)
  nlinarith

/-! ### Digits -/

/-- `valueW` on a stored word computes `EditMulticoloring.Code.value`. -/
theorem valueW_word {q : ℕ} (r : ℕ) (s : HS) (w : Word q) (hw : WordAt s (s.regs r) (s.regs (r + 1)) w)
    (hn : s.regs (r + 2) = w.length) (hq : s.regs (r + 3) = q) :
    ((valueW r).exec inp s).regs (r + 4) = value w := by
  have := (valueW_spec inp 0 r s _ (fun i hi => by rw [hq]; exact hw.lt i (by omega)) le_rfl).1
  rw [this, hn, hq]
  exact horner_value w _ (fun i h => hw i h)

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

/-! ## `repr` -/

/-! ## `words` -/

/-! ## `greedy` -/

/-! ## Writing the digits of a number -/

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

/-! ## Phase A -/

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Phase B -/

theorem params_m_le_k (q t n : ℕ) : (parameters q t n).m ≤ (parameters q t n).k :=
  Nat.le_add_right _ _

theorem encB_spec_oai (q t n p : ℕ) (hq : 2 ≤ q) (w : Word q) (hwl : w.length = (parameters q t n).k)
    (s : HS) (hs : EBase q t n p s) (hcur : s.cur = 0) :
    let s' := (encB t q).exec (RAM.inputAt w) s
    EBase q t n p s' ∧ WordAt s' 2 0 w ∧ WordAt s' (13 + 4 * t) 0 (w.take (parameters q t n).m) ∧
    s'.regs (307 + 12 * t) = (parameters q t n).m ∧ s'.regs 2 = value (w.drop (parameters q t n).m) ∧
    s'.cur = (parameters q t n).k ∧ s'.out = s.out ∧
    (encB t q).cost (RAM.inputAt w) B s ≤
      (11 * (parameters q t n).k + 7 * (parameters q t n).m + 7 * ((parameters q t n).k - (parameters q t n).m) + 40) *
        kappa B (RAM.bits (encM q t n)) := by
  intro s'
  set inp := RAM.inputAt w with hinp
  set P := parameters q t n with hP
  set M := encM q t n with hMd
  set κ := kappa B (RAM.bits M) with hκ
  have hmk : P.m ≤ P.k := params_m_le_k q t n
  have hqk : q ^ (P.k - P.m) ≤ q ^ P.k := Nat.pow_le_pow_right (by omega) (by omega)
  have hMe : M = 4 * (q ^ P.k + q ^ P.h + q ^ P.ρ + P.Q ^ 2 +
      encPW q t n + primeBound P.L + visBound q t P.m + P.h +
      P.k + P.L + P.K + n + q + t + 400) := rfl
  have hK : ∀ v, v ≤ M → kappa B (RAM.bits v) ≤ κ := fun v hv => kappa_bits_le B hv
  have rk : s.regs 116 = P.k := hs.par.hk
  have rm : s.regs 115 = P.m := hs.par.hm
  -- B0
  set s0 := (seqs [lit 40 2, lit 41 0, cp 42 116]).exec inp s with hs0
  have f0 : ∀ r, r ≠ 40 → r ≠ 41 → r ≠ 42 → s0.regs r = s.regs r := by
    intro r h1 h2 h3; simp [hs0, Function.update_apply, h1, h2, h3]
  have e40 : s0.regs 40 = 2 := by simp [hs0]
  have e41 : s0.regs 41 = 0 := by simp [hs0]
  have e42 : s0.regs 42 = P.k := by simp [hs0, rk]
  have m0 : s0.mem = s.mem := by simp [hs0]
  have cu0 : s0.cur = 0 := by simp [hs0, hcur]
  have o0 : s0.out = s.out := by simp [hs0]
  have c0 : (seqs [lit 40 2, lit 41 0, cp 42 116]).cost inp B s ≤ 3 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons, exec_lit,
      HS.setR_regs]
    simp only [Function.update_apply, show (116 : ℕ) ≠ 41 by omega, show (116 : ℕ) ≠ 40 by omega,
      if_false, rk]
    have := hK 2 (by omega); have := hK 0 (by omega); have := hK P.k (by omega)
    omega
  -- B1 readW
  obtain ⟨rd1, rd2, -, rd4, rd5, rd6, rd7⟩ := readW_spec inp B 40 s0 q M
    (fun i _ => inputAt_le w _) (by rw [e40, e41, e42, cu0]; omega)
  simp only [Nat.reduceAdd, e40, e41, e42, cu0, zero_add] at rd1 rd2 rd5 rd7
  set s1 := (readW 40).exec inp s0 with hs1
  have hw1 : WordAt s1 2 0 w := by
    intro i hi
    have := rd1 i (by omega)
    rw [zero_add, this, hinp, inputAt_sub_one w i hi]
  -- B2
  set s2 := (seqs [lit 50 2, lit 51 0, lit 52 (13 + 4 * t), lit 53 0, cp 54 115]).exec inp s1 with hs2
  have f2 : ∀ r, r ≠ 50 → r ≠ 51 → r ≠ 52 → r ≠ 53 → r ≠ 54 → s2.regs r = s1.regs r := by
    intro r h1 h2 h3 h4 h5; simp [hs2, Function.update_apply, h1, h2, h3, h4, h5]
  have r115 : s1.regs 115 = P.m := by rw [rd4 _ (by omega), f0 _ (by omega) (by omega) (by omega), rm]
  have e50 : s2.regs 50 = 2 := by simp [hs2]
  have e51 : s2.regs 51 = 0 := by simp [hs2]
  have e52 : s2.regs 52 = 13 + 4 * t := by simp [hs2]
  have e53 : s2.regs 53 = 0 := by simp [hs2]
  have e54 : s2.regs 54 = P.m := by simp [hs2, r115]
  have m2 : s2.mem = s1.mem := by simp [hs2]
  have cu2 : s2.cur = s1.cur := by simp [hs2]
  have o2 : s2.out = s1.out := by simp [hs2]
  have c2 : (seqs [lit 50 2, lit 51 0, lit 52 (13 + 4 * t), lit 53 0, cp 54 115]).cost inp B s1 ≤ 5 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons, exec_lit,
      HS.setR_regs]
    simp only [Function.update_apply, show (115 : ℕ) ≠ 50 by omega, show (115 : ℕ) ≠ 51 by omega,
      show (115 : ℕ) ≠ 52 by omega, show (115 : ℕ) ≠ 53 by omega, if_false, r115]
    have := hK 2 (by omega); have := hK 0 (by omega); have := hK P.m (by omega)
    have := hK (13 + 4 * t) (by omega)
    omega
  have hw2 : WordAt s2 2 0 w := hw1.congr (fun i _ => by simp [HS.arr, m2])
  have hnd : [50, 51, 52, 53, 54, 55, 56, 57, 58].Nodup := by decide
  have hSD : s2.regs 50 ≠ s2.regs 52 := by rw [e50, e52]; omega
  have hwx : WordAt s2 2 0 (w.take P.m) := by
    intro i hi
    simp only [List.length_take] at hi
    rw [hw2 i (by omega), List.getElem_take]
  have cw := copyW_word inp 50 51 52 53 54 55 56 57 58 s2 (w.take P.m) hnd hSD
    (by rw [e50, e51]; exact hwx) (by rw [e54, List.length_take]; omega)
  obtain ⟨-, cp2, cp3, cp4, cp5, cp6⟩ := copyW_spec inp B 50 51 52 53 54 55 56 57 58 s2 hnd hSD q M
    (fun i hi => by rw [e50, e51]; rw [e54] at hi; exact (hw2.lt i (by omega)).le)
    (by rw [e50, e51, e52, e53, e54]; omega)
  rw [e52, e53] at cw cp2
  rw [e54] at cp6
  set s3 := (copyW 50 51 52 53 54 55 56 57 58).exec inp s2 with hs3
  have hw3 : WordAt s3 2 0 w := hw2.congr (fun i _ => cp2 2 _ (by omega))
  -- B4
  set s4 := (cp (307 + 12 * t) 115).exec inp s3 with hs4
  have r115' : s3.regs 115 = P.m := by
    rw [cp3 _ (by omega) (by omega) (by omega) (by omega), f2 _ (by omega) (by omega) (by omega)
      (by omega) (by omega), r115]
  have f4 : ∀ r, r ≠ 307 + 12 * t → s4.regs r = s3.regs r := by
    intro r h; simp [hs4, Function.update_apply, h]
  have e307 : s4.regs (307 + 12 * t) = P.m := by simp [hs4, r115']
  have m4 : s4.mem = s3.mem := by simp [hs4]
  have c4 : (cp (307 + 12 * t) 115).cost inp B s3 ≤ κ := by
    simp only [cost_cp, r115']; exact hK _ (by omega)
  -- B5
  set s5 := (seqs [lit 60 2, cp 61 115, ar .sub 62 116 115, lit 63 q]).exec inp s4 with hs5
  have r116 : s4.regs 116 = P.k := by
    rw [f4 _ (by omega), cp3 _ (by omega) (by omega) (by omega) (by omega), f2 _ (by omega) (by omega)
      (by omega) (by omega) (by omega), rd4 _ (by omega), f0 _ (by omega) (by omega) (by omega), rk]
  have r115'' : s4.regs 115 = P.m := by rw [f4 _ (by omega), r115']
  have f5 : ∀ r, r ≠ 60 → r ≠ 61 → r ≠ 62 → r ≠ 63 → s5.regs r = s4.regs r := by
    intro r h1 h2 h3 h4; simp [hs5, Function.update_apply, h1, h2, h3, h4]
  have e60 : s5.regs 60 = 2 := by simp [hs5]
  have e61 : s5.regs 61 = P.m := by simp [hs5, r115'']
  have e62 : s5.regs 62 = P.k - P.m := by simp [hs5, r115'', r116]
  have e63 : s5.regs 63 = q := by simp [hs5]
  have m5 : s5.mem = s4.mem := by simp [hs5]
  have c5 : (seqs [lit 60 2, cp 61 115, ar .sub 62 116 115, lit 63 q]).cost inp B s4 ≤ 4 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, cost_ar, exec_seqs_cons, exec_lit,
      exec_cp, HS.setR_regs]
    simp only [Function.update_apply, show (115 : ℕ) ≠ 60 by omega, show (115 : ℕ) ≠ 61 by omega,
      show (116 : ℕ) ≠ 60 by omega, show (116 : ℕ) ≠ 61 by omega, show (116 : ℕ) ≠ 62 by omega,
      show (115 : ℕ) ≠ 62 by omega, if_false, r115'', r116]
    have := hK 2 (by omega); have := hK q (by omega); have := hK P.m (by omega)
    have := hK (P.k + P.m) (by omega)
    omega
  have hw5 : WordAt s5 2 0 w := hw3.congr (fun i _ => by simp [HS.arr, m5, m4])
  have hwd : WordAt s5 2 P.m (w.drop P.m) := by
    intro i hi
    simp only [List.length_drop] at hi
    have := hw5 (P.m + i) (by omega)
    rw [zero_add] at this
    rw [this, List.getElem_drop]
  have vw := valueW_word inp 60 s5 (w.drop P.m) (by rw [e60, e61]; exact hwd)
    (by rw [e62, List.length_drop, hwl]) e63
  obtain ⟨-, vf2, vf3, vf4, vf5, vf6⟩ := valueW_spec inp B 60 s5 M
    (fun i hi => by rw [e60, e61, e63]; rw [e62] at hi; exact hwd.lt i (by
      simp only [List.length_drop]; omega))
    (by rw [e60, e61, e62, e63]; omega)
  simp only [Nat.reduceAdd, e62] at vf6 vf2
  set s6 := (valueW 60).exec inp s5 with hs6
  have hs' : s' = (cp 2 64).exec inp s6 := rfl
  have e2 : s'.regs 2 = value (w.drop P.m) := by rw [hs']; simp [vw]
  have f' : ∀ r, r ≠ 2 → s'.regs r = s6.regs r := by intro r h; rw [hs']; simp [Function.update_apply, h]
  have m' : s'.mem = s6.mem := by rw [hs']; simp
  have c7 : (cp 2 64).cost inp B s6 ≤ κ := by
    simp only [cost_cp, vw]
    have h := EncS.value_lt (w.drop P.m)
    rw [List.length_drop, hwl] at h; exact hK _ (by omega)
  -- frames
  have regs' : ∀ r, (r = 1 ∨ (100 ≤ r ∧ r < 117) ∨ r = 150) → s'.regs r = s.regs r := by
    intro r hr
    rw [f' _ (by omega), vf2 _ (by omega), f5 _ (by omega) (by omega) (by omega) (by omega),
      f4 _ (by omega), cp3 _ (by omega) (by omega) (by omega) (by omega),
      f2 _ (by omega) (by omega) (by omega) (by omega) (by omega), rd4 _ (by omega),
      f0 _ (by omega) (by omega) (by omega)]
  have arr' : ∀ y i, y ≠ 2 → y ≠ 13 + 4 * t → s'.arr y i = s.arr y i := by
    intro y i h1 h2
    have a6 : s'.arr y i = s3.arr y i := by simp [HS.arr, m', vf3, m5, m4]
    rw [a6, cp2 y i (by omega)]
    have a2 : s2.arr y i = s1.arr y i := by simp [HS.arr, m2]
    rw [a2, rd2 y i (by omega)]
    simp [HS.arr, m0]
  refine ⟨hs.congr regs' (fun i => arr' 1 i (by omega) (by omega)), ?_, ?_, ?_, e2, ?_, ?_, ?_⟩
  · exact hw5.congr (fun i _ => by simp [HS.arr, m', vf3])
  · exact cw.congr (fun i _ => by simp [HS.arr, m', vf3, m5, m4])
  · rw [f' _ (by omega), vf2 _ (by omega), f5 _ (by omega) (by omega) (by omega) (by omega), e307]
  · rw [hs']; simp only [exec_cp, HS.setR_cur]; rw [vf4]; simp [hs5, hs4, cp4, cu2, rd5]
  · rw [hs']; simp only [exec_cp, HS.setR_out]; rw [vf5]; simp [hs5, hs4, cp5, o2, rd6, o0]
  · have hc : (encB t q).cost inp B s = (seqs [lit 40 2, lit 41 0, cp 42 116]).cost inp B s +
        ((readW 40).cost inp B s0 + ((seqs [lit 50 2, lit 51 0, lit 52 (13 + 4 * t), lit 53 0,
          cp 54 115]).cost inp B s1 + ((copyW 50 51 52 53 54 55 56 57 58).cost inp B s2 +
        ((cp (307 + 12 * t) 115).cost inp B s3 + ((seqs [lit 60 2, cp 61 115, ar .sub 62 116 115,
          lit 63 q]).cost inp B s4 + ((valueW 60).cost inp B s5 + ((cp 2 64).cost inp B s6 + 0))))))) := rfl
    rw [hc]
    have : (11 * P.k + 7 * P.m + 7 * (P.k - P.m) + 40) * κ = (11 * P.k + 6) * κ + (7 * P.m + 3) * κ +
        (7 * (P.k - P.m) + 4) * κ + 27 * κ := by ring
    rw [this]
    rw [← hκ] at rd7 cp6 vf6
    omega

/-! ## Phase C -/

end Phases

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.encB_spec_oai := @EditMulticoloring.Dev.Ram.encB_spec_oai
