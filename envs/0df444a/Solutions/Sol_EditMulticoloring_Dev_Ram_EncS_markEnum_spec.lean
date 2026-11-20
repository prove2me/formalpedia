-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EncS.markEnum_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:19.403057+00:00
-- url     : https://prove2.me/submissions/ca2c39c3-69b9-46c4-9ad1-876bd01524e1

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_enumScripts_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_length_le_of_mem_visits
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

theorem store_arr_ne (s : HS) {x i v y j : ℕ} (h : ¬ (y = x ∧ j = i)) :
    (s.store x i v).arr y j = s.arr y j := by simp [h]
theorem store_arr_eq (s : HS) {x i v y j : ℕ} (h : y = x ∧ j = i) :
    (s.store x i v).arr y j = v := by simp [h]

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

/-! ## `greedy` -/

/-! ## Writing the digits of a number -/

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncodeS2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Short table, part 2: marking a ball (q379, Part S)

`markBody q r a` is the enumerator body: if the visited word has length `ρ` (register `r`),
set `MARK[value w] := 1` (array id in register `r + 7`, equal to `a + 1`).
`markEnum_spec`: running the enumerator of depth `2t` with this body on a word `x` of length `ρ`
turns the mark predicate "in a ball around `chosen`" into "in a ball around `chosen ++ [x]`".

Layout (relative to `r`, `a`): registers `r` = ρ, `r+5`, `r+9` scratch, `r+7` = `a+1`,
`r+20 .. r+28` the `valueW` block, `r+30 ..` the enumerator (`shortCfg r a = ⟨r+30, a+3⟩`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

section Mark
variable (inp : ℕ → ℕ) (B : ℕ)

theorem markBody_spec {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (chosen : List (Word q)) (st0 : HS)
    (hρ : st0.regs r = ρ) (h7 : st0.regs (r + 7) = a + 1)
    (l : List (Word q)) (st : HS) (w : Word q) (hwl : w.length ≤ ρ + 2 * t)
    (hI : MInv t r a ρ chosen st0 l st) (hVL : st.regs (r + 30) = w.length)
    (hvis : WordAt st (a + 3) 0 w) :
    MInv t r a ρ chosen st0 (l ++ [w]) ((markBody q r a).exec inp st) ∧
    (∀ r', r + 30 ≤ r' → ((markBody q r a).exec inp st).regs r' = st.regs r') ∧
    (∀ y i, y ≠ a + 1 → ((markBody q r a).exec inp st).arr y i = st.arr y i) ∧
    (markBody q r a).cost inp B st ≤ (7 * ρ + 20) * kappa B (RAM.bits (shortM q t ρ a)) := by
  obtain ⟨hM, hR1, hR2, hA, hcur, hout⟩ := hI
  set M := shortM q t ρ a with hMdef
  set κ := kappa B (RAM.bits M) with hκ
  have eρ : st.regs r = ρ := (hR1 r (by omega) (by omega) (by omega)).trans hρ
  have e7 : st.regs (r + 7) = a + 1 := (hR1 _ (by omega) (by omega) (by omega)).trans h7
  have hqρ : 1 ≤ q ^ ρ := Nat.one_le_pow _ _ hq
  set s1 := (seqs [ar .sub (r + 5) (r + 30) r, ar .sub (r + 9) r (r + 30),
    ar .add (r + 5) (r + 5) (r + 9)]).exec inp st with hs1
  have r1 : ∀ r', r' ≠ r + 5 → r' ≠ r + 9 → s1.regs r' = st.regs r' := by
    intro r' h1 h2; simp (disch := omega) [hs1, upd_ne]
  have m1 : s1.mem = st.mem := by simp [hs1]
  have c1' : s1.cur = st.cur := by simp [hs1]
  have o1' : s1.out = st.out := by simp [hs1]
  have d1 : s1.regs (r + 5) = (w.length - ρ) + (ρ - w.length) := by
    simp (disch := omega) [hs1, upd_ne, hVL, eρ]
  have K0 := kappa_bits_le B (a := 0) (M := M) (by omega)
  have hc1 : (seqs [ar .sub (r + 5) (r + 30) r, ar .sub (r + 9) r (r + 30),
      ar .add (r + 5) (r + 5) (r + 9)]).cost inp B st ≤ 3 * κ := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, exec_ar,
      cost_ar, HS.setR_regs, upd_ne, upd_eq, hVL, eρ, arith_sub, arith_add]
    have := kappa_bits_le B (a := w.length + ρ) (M := M) (by rw [hMdef, shortM]; omega)
    have := kappa_bits_le B (a := ρ + w.length) (M := M) (by rw [hMdef, shortM]; omega)
    have := kappa_bits_le B (a := w.length - ρ + (ρ - w.length)) (M := M)
      (by rw [hMdef, shortM]; omega)
    omega
  by_cases hd : (w.length - ρ) + (ρ - w.length) = 0
  · have hwρ : w.length = ρ := by omega
    set s2 := (seqs [lit (r + 20) (a + 3), lit (r + 21) 0, cp (r + 22) r, lit (r + 23) q]).exec inp s1
      with hs2
    have r2 : ∀ r', (r' < r + 20 ∨ r + 24 ≤ r') → s2.regs r' = s1.regs r' := by
      intro r' h; simp (disch := omega) [hs2, upd_ne]
    have m2 : s2.mem = st.mem := by simp [hs2, m1]
    have v0 : s2.regs (r + 20) = a + 3 := by simp (disch := omega) [hs2, upd_ne]
    have v1 : s2.regs (r + 21) = 0 := by simp (disch := omega) [hs2, upd_ne]
    have v2 : s2.regs (r + 22) = ρ := by
      simp (disch := omega) [hs2, upd_ne]; rw [r1 r (by omega) (by omega), eρ]
    have v3 : s2.regs (r + 23) = q := by simp (disch := omega) [hs2, upd_ne]
    have hw2 : WordAt s2 (s2.regs (r + 20)) (s2.regs (r + 21)) w := by
      rw [v0, v1]; exact hvis.congr (fun i _ => by simp [HS.arr, m2])
    have hval := valueW_word inp (r + 20) s2 w hw2 (by rw [v2, hwρ]) v3
    obtain ⟨-, w2, w3, w4, w5, w6⟩ := valueW_spec inp B (r + 20) s2 M
      (fun i hi => by rw [v0, v1, v3]; rw [v2] at hi; exact hvis.lt i (by omega) |>.trans_eq' (by
        simp [HS.arr, m2]))
      (by rw [v0, v1, v2, v3, hMdef, shortM]; omega)
    set s3 := (valueW (r + 20)).exec inp s2 with hs3
    have hvlt : value w < q ^ ρ := hwρ ▸ value_lt w
    have hex : (markBody q r a).exec inp st =
        (s3.setR (r + 9) 1).store (a + 1) (value w) 1 := by
      have e : (markBody q r a).exec inp st = (Cmd.ifz (r + 5) (.seq (seqs [lit (r + 20) (a + 3),
          lit (r + 21) 0, cp (r + 22) r, lit (r + 23) q]) (.seq (valueW (r + 20))
          (seqs [lit (r + 9) 1, ast (r + 7) (r + 24) (r + 9)]))) .skip).exec inp s1 := rfl
      rw [e, exec_ifz, if_pos (by rw [d1]; exact hd)]
      show (seqs [lit (r + 9) 1, ast (r + 7) (r + 24) (r + 9)]).exec inp s3 = _
      have e7' : s3.regs (r + 7) = a + 1 := by
        rw [w2 _ (by omega), r2 _ (by omega), r1 _ (by omega) (by omega), e7]
      simp only [exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ast]
      simp (disch := omega) only [HS.setR_regs, upd_ne, upd_eq]
      rw [e7', hval]
    have r3 : ∀ r', r' ≠ r + 5 → r' ≠ r + 9 → (r' < r + 20 ∨ r + 29 ≤ r') →
        ((s3.setR (r + 9) 1).store (a + 1) (value w) 1).regs r' = st.regs r' := by
      intro r' h1 h2 h3
      simp (disch := omega) only [HS.store_regs, HS.setR_regs, upd_ne]
      rw [w2 _ (by omega), r2 _ (by omega), r1 _ h1 h2]
    have a3 : ∀ y i, ¬ (y = a + 1 ∧ i = value w) →
        ((s3.setR (r + 9) 1).store (a + 1) (value w) 1).arr y i = st.arr y i := by
      intro y i h
      rw [store_arr_ne _ h]; simp [HS.arr, w3, m2]
    rw [hex]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro u hu
      by_cases huw : u = value w
      · subst huw
        rw [store_arr_eq _ ⟨rfl, rfl⟩, repr_value w ρ hwρ, if_pos (Or.inr (by simp))]
      · rw [a3 _ _ (fun h => huw h.2), hM u hu]
        have hne : Code.repr q ρ u ≠ w := by
          intro h; apply huw; rw [← h, value_repr hq ρ u hu]
        simp [hne]
    · intro r' h1 h2 h3; rw [r3 r' h2 h3 (by omega)]; exact hR1 r' h1 h2 h3
    · intro r' h; rw [r3 r' (by omega) (by omega) (by omega)]; exact hR2 r' h
    · intro y i h1 h2; rw [a3 y i (fun h => h1 h.1)]; exact hA y i h1 h2
    · show ((s3.setR (r + 9) 1).store (a + 1) (value w) 1).cur = st0.cur
      rw [HS.store_cur, HS.setR_cur, w4]; simp [hs2, c1', hcur]
    · show ((s3.setR (r + 9) 1).store (a + 1) (value w) 1).out = st0.out
      rw [HS.store_out, HS.setR_out, w5]; simp [hs2, o1', hout]
    · intro r' h; exact r3 r' (by omega) (by omega) (by omega)
    · intro y i h; exact a3 y i (fun h' => h h'.1)
    · have hc : (markBody q r a).cost inp B st =
          (seqs [ar .sub (r + 5) (r + 30) r, ar .sub (r + 9) r (r + 30),
            ar .add (r + 5) (r + 5) (r + 9)]).cost inp B st +
          (kappa B (RAM.bits (s1.regs (r + 5))) +
          ((seqs [lit (r + 20) (a + 3), lit (r + 21) 0, cp (r + 22) r, lit (r + 23) q]).cost inp B s1 +
          ((valueW (r + 20)).cost inp B s2 +
          ((lit (r + 9) 1).cost inp B s3 +
          (ast (r + 7) (r + 24) (r + 9)).cost inp B (s3.setR (r + 9) 1))))) := by
        have e : (markBody q r a).cost inp B st = _ + (Cmd.ifz (r + 5) (.seq (seqs [lit (r + 20) (a + 3),
            lit (r + 21) 0, cp (r + 22) r, lit (r + 23) q]) (.seq (valueW (r + 20))
            (seqs [lit (r + 9) 1, ast (r + 7) (r + 24) (r + 9)]))) .skip).cost inp B s1 := rfl
        rw [e, cost_ifz, if_pos (by rw [d1]; exact hd)]
        simp only [cost_seq, cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, exec_seqs_nil, add_zero]
        rfl
      rw [hc, d1, hd]
      have c2 : (seqs [lit (r + 20) (a + 3), lit (r + 21) 0, cp (r + 22) r,
          lit (r + 23) q]).cost inp B s1 ≤ 4 * κ := by
        simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
          exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne]
        rw [r1 r (by omega) (by omega), eρ]
        have := kappa_bits_le B (a := a + 3) (M := M) (by rw [hMdef, shortM]; omega)
        have := kappa_bits_le B (a := ρ) (M := M) (by rw [hMdef, shortM]; omega)
        have := kappa_bits_le B (a := q) (M := M) (by rw [hMdef, shortM]; omega)
        omega
      have c3 : (valueW (r + 20)).cost inp B s2 ≤ (7 * ρ + 4) * κ := by rw [v2] at w6; exact w6
      have c4 : (lit (r + 9) 1).cost inp B s3 ≤ κ := by
        rw [cost_lit]; exact kappa_bits_le B (by rw [hMdef, shortM]; omega)
      have c5 : (ast (r + 7) (r + 24) (r + 9)).cost inp B (s3.setR (r + 9) 1) ≤ κ := by
        rw [cost_ast]
        simp (disch := omega) only [HS.setR_regs, upd_ne, upd_eq]
        have e7' : s3.regs (r + 7) = a + 1 := by
          rw [w2 _ (by omega), r2 _ (by omega), r1 _ (by omega) (by omega), e7]
        rw [e7', hval]
        exact kappa_bits_le B (by rw [hMdef, shortM]; omega)
      have : (7 * ρ + 20) * κ = 3 * κ + κ + 4 * κ + (7 * ρ + 4) * κ + κ + κ + 6 * κ := by ring
      omega
  · have hex : (markBody q r a).exec inp st = s1 := by
      show (Cmd.ifz (r + 5) _ .skip).exec inp s1 = _
      rw [exec_ifz, if_neg (by rw [d1]; exact hd)]; rfl
    have hwρ : w.length ≠ ρ := by omega
    rw [hex]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro u hu
      rw [show s1.arr (a + 1) u = st.arr (a + 1) u by simp [HS.arr, m1], hM u hu]
      have hne : Code.repr q ρ u ≠ w := by
        intro h; apply hwρ; rw [← h, repr_length hq]
      simp [hne]
    · intro r' h1 h2 h3; rw [r1 r' h2 h3]; exact hR1 r' h1 h2 h3
    · intro r' h; rw [r1 r' (by omega) (by omega)]; exact hR2 r' h
    · intro y i h1 h2; rw [show s1.arr y i = st.arr y i by simp [HS.arr, m1]]; exact hA y i h1 h2
    · rw [c1', hcur]
    · rw [o1', hout]
    · intro r' h; exact r1 r' (by omega) (by omega)
    · intro y i _; simp [HS.arr, m1]
    · have hc : (markBody q r a).cost inp B st =
          (seqs [ar .sub (r + 5) (r + 30) r, ar .sub (r + 9) r (r + 30),
            ar .add (r + 5) (r + 5) (r + 9)]).cost inp B st +
          (kappa B (RAM.bits (s1.regs (r + 5))) + 0) := by
        show _ + (Cmd.ifz (r + 5) _ .skip).cost inp B s1 = _
        rw [cost_ifz, if_neg (by rw [d1]; exact hd)]; rfl
      rw [hc, d1]
      have := kappa_bits_le B (a := w.length - ρ + (ρ - w.length)) (M := M)
        (by rw [hMdef, shortM]; omega)
      have : (7 * ρ + 20) * κ = 4 * κ + (7 * ρ + 16) * κ := by ring
      omega

theorem foldl_snoc {β : Type*} (L acc : List β) : L.foldl (fun l w => l ++ [w]) acc = acc ++ L := by
  induction L generalizing acc with
  | nil => simp
  | cons w L ih => rw [List.foldl_cons, ih]; simp

theorem mem_ball_iff_visits {q : ℕ} (s : ℕ) (x u : Word q) : u ∈ ball s x ↔ u ∈ visits s x := by
  simp [ball, visits]

/-- One enumeration with `markBody`: the marks gain the ball of radius `2t` around `x`. -/
theorem markEnum_spec_oai {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (chosen : List (Word q)) (st0 : HS)
    (hρ : st0.regs r = ρ) (h7 : st0.regs (r + 7) = a + 1)
    (x : Word q) (hx : x.length = ρ) (st : HS) (hI : MInv t r a ρ chosen st0 [] st)
    (hlen : st.regs ((shortCfg r a).lenR (2 * t)) = x.length)
    (hbuf : WordAt st ((shortCfg r a).buf (2 * t)) 0 x) :
    MInv t r a ρ (chosen ++ [x]) st0 []
      ((enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).exec inp st) ∧
    (enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).cost inp B st ≤
      (visits (2 * t) x).length * ((7 * ρ + 20) * kappa B (RAM.bits (shortM q t ρ a)) +
        (shortCfg r a).enumE B q ρ (2 * t)) := by
  have E := enumScripts_spec (2 * t) (shortCfg r a) (markBody q r a) inp B
    (MInv t r a ρ chosen st0) (fun l w => l ++ [w]) ((7 * ρ + 20) * kappa B (RAM.bits (shortM q t ρ a)))
    x []
    (by
      intro l s1 s2 ⟨h1, h2, h3, h4, h5, h6⟩ ⟨g1, g2, g3, g4⟩
      have nr : ∀ r', (r' < r + 30 ∨ r + 49 + 6 * t ≤ r') → s2.regs r' = s1.regs r' := by
        intro r' h; apply g1; simp only [EnumCfg.ownsReg, shortCfg]; omega
      have na : ∀ y i, (y < a + 3 ∨ a + 5 + 2 * t ≤ y) → s2.arr y i = s1.arr y i := by
        intro y i h; apply g2; simp only [EnumCfg.ownsArr, shortCfg]; omega
      refine ⟨fun u hu => (na _ _ (by omega)).trans (h1 u hu),
        fun r' a1 a2 a3 => (nr r' (by omega)).trans (h2 r' a1 a2 a3),
        fun r' a1 => (nr r' (by omega)).trans (h3 r' a1),
        fun y i a1 a2 => (na y i a2).trans (h4 y i a1 a2), g3.trans h5, g4.trans h6⟩)
    (by
      intro l s1 w j hj hw _ hInv hVL hvis
      have hwmem : w ∈ visits (2 * t) x := hw ▸ List.getElem_mem hj
      have hwl := length_le_of_mem_visits (2 * t) x hwmem
      obtain ⟨b1, b2, b3, b4⟩ := markBody_spec inp B hq t r a ρ chosen st0 hρ h7 l s1 w (by omega)
        hInv hVL hvis
      refine ⟨b1, ⟨fun r' hr _ => b2 r' ?_, fun y i hy _ => b3 y i ?_⟩, b4⟩
      · simp only [EnumCfg.ownsReg, shortCfg] at hr; omega
      · simp only [EnumCfg.ownsArr, shortCfg] at hy; omega)
    st hlen hbuf hI
  obtain ⟨E1, -, -, E4⟩ := E
  rw [foldl_snoc, List.nil_append] at E1
  refine ⟨?_, by rw [hx] at E4; exact E4⟩
  obtain ⟨h1, h2⟩ := E1
  refine ⟨fun u hu => ?_, h2⟩
  rw [h1 u hu]
  congr 1
  apply propext
  simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨z, hz, h⟩ | h)
    · exact ⟨z, Or.inl hz, h⟩
    · exact ⟨x, Or.inr rfl, (mem_ball_iff_visits _ _ _).mpr h⟩
  · rintro ⟨z, hz | rfl, h⟩
    · exact Or.inl ⟨z, hz, h⟩
    · exact Or.inr ((mem_ball_iff_visits _ _ _).mp h)

end Mark

end EditMulticoloring.Dev.Ram.EncS
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EncS.markEnum_spec_oai := @EditMulticoloring.Dev.Ram.EncS.markEnum_spec_oai
