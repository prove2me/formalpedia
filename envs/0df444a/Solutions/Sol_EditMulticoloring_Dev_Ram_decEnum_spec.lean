-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.decEnum_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:21.626785+00:00
-- url     : https://prove2.me/submissions/1745c0fa-b0ed-4b5e-9544-3f53488db1ea

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_enumScripts_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_length_le_of_mem_visits
import Theorems.Thm_EditMulticoloring_Dev_Ram_pC5_spec
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

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

section Init
variable (inp : ℕ → ℕ) (B : ℕ)

theorem value_lt {q : ℕ} (x : Word q) : value x < q ^ x.length ∨ x = [] := by
  rcases x with _ | ⟨a, x⟩
  · right; rfl
  · left
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have := horner_lt q (fun i => ((a :: x)[i]?.map Fin.val).getD 0) (a :: x).length (by
      intro i hi
      simp only [List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
      exact (a :: x)[i].isLt) _ le_rfl
    rwa [horner_value (a :: x) _ (fun i h => by simp [List.getElem?_eq_getElem h])] at this

end Init

/-! ## Enumeration: digits of every neighbour -/

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

end Dec1

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

theorem le_primeBound (L : ℕ) : 6 * (L + 2) + 1 ≤ primeBound L := by
  unfold primeBound
  have : 6 ≤ 2 * (Nat.log 2 (L + 2) + 3) := by omega
  nlinarith

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

theorem validate_unfold {q : ℕ} (t n p : ℕ) (c : Word q) (hc : c.length = n) :
    validate t n p c = (shortInverse t (parameters q t n).h (c.drop (parameters q t n).m)).bind
      (fun s => vMid t (parameters q t n) p (c.take (parameters q t n).m)
        (value (s.take (parameters q t n).h₁)) (value (s.drop (parameters q t n).h₁))) := by
  unfold validate
  simp only [hc, ne_eq, not_true_eq_false, if_false]
  rcases shortInverse t (parameters q t n).h (c.drop (parameters q t n).m) with _ | s
  · rfl
  · simp only [Option.bind_some, vMid, vTail]
    rfl

theorem validate_len {q : ℕ} (t n p : ℕ) (c : Word q) (hc : c.length ≠ n) :
    validate t n p c = none := by
  unfold validate; simp [hc]

theorem dec_foldl_or_eq_findSome {α β : Type*} (g : α → Option β) (l : List α) :
    l.foldl (fun a w => a.or (g w)) none = l.findSome? g := by
  have key : ∀ (l : List α) (b : β), l.foldl (fun a w => a.or (g w)) (some b) = some b := by
    intro l; induction l with
    | nil => intro b; rfl
    | cons w l ih => intro b; simp only [List.foldl_cons, Option.some_or]; exact ih b
  induction l with
  | nil => rfl
  | cons w l ih =>
    simp only [List.foldl_cons, Option.none_or, List.findSome?_cons]
    rcases hg : g w with _ | b
    · exact ih
    · exact key l b

theorem WordAt.dropD {q : ℕ} {s : HS} {X : ℕ} {w : Word q} (hw : WordAt s X 0 w) (m : ℕ) :
    WordAt s X m (w.drop m) := by
  intro i hi
  rw [List.length_drop] at hi
  rw [List.getElem_drop]; have := hw (m + i) (by omega); rw [zero_add] at this; exact this

/-! ## Layout -/

theorem SFr.refl (t : ℕ) (st : HS) : SFr t st st := ⟨fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩

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

theorem dec_m_le_k (q t n : ℕ) : (parameters q t n).m ≤ (parameters q t n).k := by
  show (parameters q t n).m ≤ (parameters q t n).m + floorLog q (parameters q t n).J
  omega

section Levels
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Level 8: store the result `x ++ repr q (k - m) j` and set the done flag -/

/-! ## Level 7: count the good indices below `i`, compare with `J`, store -/

/-! ## Level 6: compare `η` with the colour of `x` modulo `primeAt i` -/

/-! ## Level 5: the colours (`colorsAll`), the test `localGood x i` -/

/-! ## Level 4: `pi := PR[i]`, test `η < pi` -/

theorem pC4_spec {q t n p : ℕ} (H : DHyp q t n p)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (i η : ℕ) (hi : st.regs 213 = i) (hiL : i < (parameters q t n).L)
    (hη : st.regs 214 = η) (hηb : η ≤ q ^ (parameters q t n).h) :
    DOut t st ((pC4 q t).exec inp st)
      (if η ≥ primeAt i then none else vTail t (parameters q t n) p (w.take (parameters q t n).m) i η) ∧
    (pC4 q t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 14 * n +
      7 * (parameters q t n).k + 11 * dVb q t n + 73) * kappa B (RAM.bits (DM q t n)) + caCost q t n B := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have prt : ∀ i ≤ P.L, st.arr 1 i = primeAt i := hc.prt
  have hpb := primeAt_lt_primeBound (L := P.L) (i := i) hiL.le
  have hpb2 := le_primeBound P.L
  set A := seqs [ald 215 1 213, ar .lt 212 214 215] with hA
  set s1 := A.exec inp st with hs1
  have hfr := sfr_of_block inp t A (by
      intro r hr; simp only [hA, seqs, Cmd.wregs, ar, ald, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.nil_append, List.append_nil] at hr; omega)
    rfl rfl rfl st
  have v215 : s1.regs 215 = primeAt i := by
    simp (disch := omega) [hs1, hA, upd_ne, hc.pr1, hi]; exact prt i hiL.le
  have v212 : s1.regs 212 = if η < primeAt i then 1 else 0 := by
    simp (disch := omega) [hs1, hA, upd_ne, hc.pr1, hi, hη]; rw [prt i hiL.le]
  have R : ∀ r, (r < 212 ∨ 216 ≤ r ∨ r = 213 ∨ r = 214) → s1.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs1, hA, upd_ne]
  have c1 : A.cost inp B st ≤ 2 * κ := by
    simp (disch := omega) only [hA, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ald, exec_seqs_cons,
      exec_ar, exec_ald, HS.setR_regs, upd_ne, upd_eq, hc.pr1, hi, hη]
    rw [prt i hiL.le]
    have := kb (1 + i + primeAt i) (by omega)
    have := kb (η + primeAt i) (by omega)
    omega
  have hex : (pC4 q t).exec inp st = (Cmd.ifz 212 .skip (pC5 q t)).exec inp s1 := rfl
  have hco : (pC4 q t).cost inp B st = A.cost inp B st + (Cmd.ifz 212 .skip (pC5 q t)).cost inp B s1 := rfl
  have hk := kb (s1.regs 212) (by rw [v212]; split_ifs <;> omega)
  rw [hex, hco]
  by_cases hlt : η < primeAt i
  · have hz : s1.regs 212 ≠ 0 := by rw [v212, if_pos hlt]; omega
    have hc1 := hc.of_SFr hfr.1
    have hw1 : WordAt s1 (dC0 t).a0 0 w := hw.congr (fun i _ => hfr.1.2.1 _ _ (Or.inr (by simp [dC0])))
    obtain ⟨D1, D2⟩ := pC5_spec inp B H.hq H.H3 H.hcol H.hp H.hpW H.hQ0 H.hQW s1 hc1 w hw1 hwl i η
      (by rw [R _ (by omega), hi]) hiL (by rw [R _ (by omega), hη]) hlt v215
    have D2' : (pC5 q t).cost inp B s1 ≤ ((11 * dVb q t n + 11) * P.L + 14 * n +
      7 * P.k + 11 * dVb q t n + 70) * κ + caCost q t n B := D2
    rw [if_neg (by omega)]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_neg hz]; exact DOut.pre hfr.1 hfr.2 D1
    · rw [cost_ifz, if_neg hz]
      have h3 : ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 73) * κ =
        ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 70) * κ + 3 * κ := by ring
      rw [h3]; omega
  · have hz : s1.regs 212 = 0 := by rw [v212, if_neg hlt]
    rw [if_pos (by omega)]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_pos hz]; exact DOut.none_of_SFr hfr.1 hfr.2
    · rw [cost_ifz, if_pos hz, cost_skip]
      have h3 : ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 73) * κ =
        ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 70) * κ + 3 * κ := by ring
      rw [h3]
      have := Nat.zero_le (((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 70) * κ)
      omega

/-! ## Level 3: `i := idx / q^h₂`, `η := idx % q^h₂`, test `i < L` -/

theorem pC3_spec {q t n p : ℕ} (H : DHyp q t n p)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (idx : ℕ) (hidx : st.regs 211 = idx) (hidxb : idx < q ^ (parameters q t n).h) :
    DOut t st ((pC3 q t).exec inp st)
      (vMid t (parameters q t n) p (w.take (parameters q t n).m) (idx / q ^ (parameters q t n).h₂)
        (idx % q ^ (parameters q t n).h₂)) ∧
    (pC3 q t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 14 * n +
      7 * (parameters q t n).k + 11 * dVb q t n + 77) * kappa B (RAM.bits (DM q t n)) + caCost q t n B := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have hpb2 := le_primeBound P.L
  have h3 : st.regs 3 = q ^ P.h₂ := hc.qh2
  have h105 : st.regs 105 = P.L := hc.par.hL
  have hh : P.h = P.h₁ + P.h₂ := rfl
  have hq2 : q ^ P.h₂ ≤ q ^ P.h := Nat.pow_le_pow_right (by have := H.hq; omega) (by omega)
  set i := idx / q ^ P.h₂ with hidef
  set η := idx % q ^ P.h₂ with hηdef
  have hile : i ≤ idx := Nat.div_le_self _ _
  have hηle : η ≤ idx := Nat.mod_le _ _
  set A := seqs [ar .div 213 211 3, ar .mod 214 211 3, ar .lt 212 213 105] with hA
  set s1 := A.exec inp st with hs1
  have hfr := sfr_of_block inp t A (by
      intro r hr; simp only [hA, seqs, Cmd.wregs, ar, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.nil_append, List.append_nil] at hr; omega)
    rfl rfl rfl st
  have v213 : s1.regs 213 = i := by simp (disch := omega) [hs1, hA, upd_ne, hidx, h3, hidef]
  have v214 : s1.regs 214 = η := by simp (disch := omega) [hs1, hA, upd_ne, hidx, h3, hηdef]
  have v212 : s1.regs 212 = if i < P.L then 1 else 0 := by
    simp (disch := omega) [hs1, hA, upd_ne, hidx, h3, h105, hidef]
  have c1 : A.cost inp B st ≤ 3 * κ := by
    simp (disch := omega) only [hA, cost_seqs_cons, cost_seqs_nil, cost_ar, exec_seqs_cons,
      exec_ar, HS.setR_regs, upd_ne, upd_eq, hidx, h3, h105, arith_div]
    have := kb (idx + q ^ P.h₂) (by omega)
    have := kb (idx / q ^ P.h₂ + P.L) (by omega)
    omega
  have hex : (pC3 q t).exec inp st = (Cmd.ifz 212 .skip (pC4 q t)).exec inp s1 := rfl
  have hco : (pC3 q t).cost inp B st = A.cost inp B st + (Cmd.ifz 212 .skip (pC4 q t)).cost inp B s1 := rfl
  have hk := kb (s1.regs 212) (by rw [v212]; split_ifs <;> omega)
  rw [hex, hco]
  unfold vMid
  by_cases hlt : i < P.L
  · have hz : s1.regs 212 ≠ 0 := by rw [v212, if_pos hlt]; omega
    have hc1 := hc.of_SFr hfr.1
    have hw1 : WordAt s1 (dC0 t).a0 0 w := hw.congr (fun i _ => hfr.1.2.1 _ _ (Or.inr (by simp [dC0])))
    obtain ⟨D1, D2⟩ := pC4_spec inp B H s1 hc1 w hw1 hwl i η v213 hlt v214 (show η ≤ q ^ P.h by omega)
    have D2' : (pC4 q t).cost inp B s1 ≤ ((11 * dVb q t n + 11) * P.L + 14 * n +
      7 * P.k + 11 * dVb q t n + 73) * κ + caCost q t n B := D2
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_neg hz]
      have e : (if i ≥ P.L ∨ η ≥ primeAt i then none else vTail t P p (w.take P.m) i η) =
          (if η ≥ primeAt i then none else vTail t P p (w.take P.m) i η) := by
        by_cases h2 : η ≥ primeAt i
        · simp [h2]
        · simp [h2, show ¬ i ≥ P.L by omega]
      rw [e]; exact DOut.pre hfr.1 hfr.2 D1
    · rw [cost_ifz, if_neg hz]
      have h3 : ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 77) * κ =
        ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 73) * κ + 4 * κ := by ring
      rw [h3]; omega
  · have hz : s1.regs 212 = 0 := by rw [v212, if_neg hlt]
    rw [if_pos (Or.inl (by omega))]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_pos hz]; exact DOut.none_of_SFr hfr.1 hfr.2
    · rw [cost_ifz, if_pos hz, cost_skip]
      have h3 : ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 77) * κ =
        ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 73) * κ + 4 * κ := by ring
      rw [h3]
      have := Nat.zero_le (((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 73) * κ)
      omega

/-! ## Level 2: `idx := INV - 1`, test `idx < q^h` -/

theorem pC2_spec {q t n p : ℕ} (H : DHyp q t n p)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (inv : ℕ) (hinv : st.regs 210 = inv) (hinvb : inv ≤ q ^ n) :
    DOut t st ((pC2 q t).exec inp st)
      (if inv - 1 < q ^ (parameters q t n).h then
        vMid t (parameters q t n) p (w.take (parameters q t n).m) ((inv - 1) / q ^ (parameters q t n).h₂)
          ((inv - 1) % q ^ (parameters q t n).h₂) else none) ∧
    (pC2 q t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 14 * n +
      7 * (parameters q t n).k + 11 * dVb q t n + 81) * kappa B (RAM.bits (DM q t n)) + caCost q t n B := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have h112 : st.regs 112 = q ^ P.h := hc.par.hqh
  set A := seqs [lit 217 1, ar .sub 211 210 217, ar .lt 212 211 112] with hA
  set s1 := A.exec inp st with hs1
  have hfr := sfr_of_block inp t A (by
      intro r hr; simp only [hA, seqs, Cmd.wregs, ar, lit, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.nil_append, List.append_nil] at hr; omega)
    rfl rfl rfl st
  have v211 : s1.regs 211 = inv - 1 := by simp (disch := omega) [hs1, hA, upd_ne, hinv]
  have v212 : s1.regs 212 = if inv - 1 < q ^ P.h then 1 else 0 := by
    simp (disch := omega) [hs1, hA, upd_ne, hinv, h112]
  have c1 : A.cost inp B st ≤ 3 * κ := by
    simp (disch := omega) only [hA, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_lit, exec_seqs_cons,
      exec_ar, exec_lit, HS.setR_regs, upd_ne, upd_eq, hinv, h112, arith_sub]
    have := kb 1 (by omega)
    have := kb (inv + 1) (by omega)
    have := kb (inv - 1 + q ^ P.h) (by omega)
    omega
  have hex : (pC2 q t).exec inp st = (Cmd.ifz 212 .skip (pC3 q t)).exec inp s1 := rfl
  have hco : (pC2 q t).cost inp B st = A.cost inp B st + (Cmd.ifz 212 .skip (pC3 q t)).cost inp B s1 := rfl
  have hk := kb (s1.regs 212) (by rw [v212]; split_ifs <;> omega)
  rw [hex, hco]
  by_cases hlt : inv - 1 < q ^ P.h
  · have hz : s1.regs 212 ≠ 0 := by rw [v212, if_pos hlt]; omega
    have hc1 := hc.of_SFr hfr.1
    have hw1 : WordAt s1 (dC0 t).a0 0 w := hw.congr (fun i _ => hfr.1.2.1 _ _ (Or.inr (by simp [dC0])))
    obtain ⟨D1, D2⟩ := pC3_spec inp B H s1 hc1 w hw1 hwl (inv - 1) v211 hlt
    have D2' : (pC3 q t).cost inp B s1 ≤ ((11 * dVb q t n + 11) * P.L + 14 * n +
      7 * P.k + 11 * dVb q t n + 77) * κ + caCost q t n B := D2
    rw [if_pos hlt]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_neg hz]; exact DOut.pre hfr.1 hfr.2 D1
    · rw [cost_ifz, if_neg hz]
      have h3 : ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 81) * κ =
        ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 77) * κ + 4 * κ := by ring
      rw [h3]; omega
  · have hz : s1.regs 212 = 0 := by rw [v212, if_neg hlt]
    rw [if_neg hlt]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_pos hz]; exact DOut.none_of_SFr hfr.1 hfr.2
    · rw [cost_ifz, if_pos hz, cost_skip]
      have h3 : ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 81) * κ =
        ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 77) * κ + 4 * κ := by ring
      rw [h3]
      have := Nat.zero_le (((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 77) * κ)
      omega

/-! ## The candidate test: value of the tail, `INV` lookup -/

theorem dec_value_lt_pow {q : ℕ} (hq : 0 < q) (x : Word q) : value x < q ^ x.length := by
  rcases value_lt x with h | rfl
  · exact h
  · simp [value]

set_option maxHeartbeats 800000 in
theorem pCand_spec {q t n p : ℕ} (H : DHyp q t n p) (hsplit : SplitOK q t n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) :
    DOut t st ((pCand q t).exec inp st) (validate t n p w) ∧
    (pCand q t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 21 * n +
      7 * (parameters q t n).k + 11 * dVb q t n + 100) * kappa B (RAM.bits (DM q t n)) + caCost q t n B := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have hq := H.hq
  have H3 : P.m + P.ρ = n := H.H3
  have hmn : P.m ≤ n := params_m_le q t n
  have hm115 : st.regs 115 = P.m := hc.par.hm
  have hρ113 : st.regs 113 = P.ρ := hc.par.hρ
  have invf : ∀ z : Word q, z.length = P.ρ → shortInverse t P.h z =
      if st.arr (dINV t) (value z) ≠ 0 ∧ st.arr (dINV t) (value z) - 1 < q ^ P.h
      then some (Code.repr q P.h (st.arr (dINV t) (value z) - 1)) else none := hc.inv
  have invb : ∀ u < q ^ P.ρ, st.arr (dINV t) u ≤ q ^ P.ρ := hc.invb
  have hqρ : q ^ P.ρ ≤ q ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  set z := w.drop P.m with hz
  have hzl : z.length = P.ρ := by rw [hz, List.length_drop]; omega
  have hvz : value z < q ^ P.ρ := hzl ▸ dec_value_lt_pow (by omega) z
  -- block A
  set A0 := seqs [lit 200 (14 + 4 * t), cp 201 115, cp 202 113, cp 203 4] with hA0
  set s0 := A0.exec inp st with hs0
  have r0 : ∀ r, (r < 200 ∨ 204 ≤ r) → s0.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs0, hA0, upd_ne]
  have m0 : s0.mem = st.mem := by simp [hs0, hA0]
  have w200 : s0.regs 200 = 14 + 4 * t := by simp (disch := omega) [hs0, hA0, upd_ne]
  have w201 : s0.regs 201 = P.m := by simp (disch := omega) [hs0, hA0, upd_ne, hm115]
  have w202 : s0.regs 202 = P.ρ := by simp (disch := omega) [hs0, hA0, upd_ne, hρ113]
  have w203 : s0.regs 203 = q := by simp (disch := omega) [hs0, hA0, upd_ne, hc.q4]
  have c0 : A0.cost inp B st ≤ 4 * κ := by
    simp (disch := omega) only [hA0, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_lit, exec_cp, HS.setR_regs, upd_ne, hm115, hρ113, hc.q4]
    have := kb (14 + 4 * t) (by omega)
    have := kb P.m (by omega)
    have := kb P.ρ (by omega)
    have := kb q (by omega)
    omega
  have hz0 : WordAt s0 (s0.regs 200) (s0.regs (200 + 1)) z := by
    rw [w200, w201]
    exact (hw.dropD P.m).congr (fun i _ => by simp [HS.arr, m0, dC0])
  have hval := valueW_word inp 200 s0 z hz0 (by rw [w202, hzl]) w203
  obtain ⟨-, vr, vm, vcur, vout, vcost⟩ := valueW_spec inp B 200 s0 (DM q t n)
    (fun i hi => by rw [w203]; rw [w202] at hi; exact hz0.lt i (by omega))
    (by rw [w200, w201, w202, w203]; omega)
  rw [w202] at vcost
  set s1 := (valueW 200).exec inp s0 with hs1
  set inv := st.arr (dINV t) (value z) with hinv
  have hinvb : inv ≤ q ^ P.ρ := invb _ hvz
  set A2 := seqs [lit 216 (dINV t), ald 210 216 204] with hA2
  set s2 := A2.exec inp s1 with hs2
  have v210 : s2.regs 210 = inv := by
    simp (disch := omega) [hs2, hA2, upd_ne, hval]
    simp [HS.arr, vm, m0, hinv]
  have c2 : A2.cost inp B s1 ≤ 2 * κ := by
    simp (disch := omega) only [hA2, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ald,
      exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, upd_eq, hval, HS.setR_arr]
    have e : s1.arr (dINV t) (value z) = inv := by simp [HS.arr, vm, m0, hinv]
    rw [e]
    have := kb (dINV t) (by unfold dINV; omega)
    have := kb (dINV t + value z + inv) (by unfold dINV; omega)
    omega
  set A := seqs [A0, valueW 200, A2] with hA
  have hsA : A.exec inp st = s2 := rfl
  have hfr := sfr_of_block inp t A (by
      intro r hr; simp only [hA, hA0, hA2, valueW, forLoop, seqs, Cmd.wregs, ar, lit, cp, ald,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.nil_append,
        List.append_nil] at hr; omega)
    rfl rfl rfl st
  rw [hsA] at hfr
  have hex : (pCand q t).exec inp st = (Cmd.ifz 210 .skip (pC2 q t)).exec inp s2 := rfl
  have hco : (pCand q t).cost inp B st = A0.cost inp B st + ((valueW 200).cost inp B s0 +
      (A2.cost inp B s1 + 0)) + (Cmd.ifz 210 .skip (pC2 q t)).cost inp B s2 := rfl
  have vcost' : (valueW 200).cost inp B s0 ≤ (7 * n + 4) * κ :=
    vcost.trans (Nat.mul_le_mul_right _ (by omega))
  have hk := kb (s2.regs 210) (by rw [v210]; omega)
  have hval_eq : validate t n p w = (if inv ≠ 0 ∧ inv - 1 < q ^ P.h then
      vMid t P p (w.take P.m) ((inv - 1) / q ^ P.h₂) ((inv - 1) % q ^ P.h₂) else none) := by
    rw [validate_unfold t n p w hwl, ← hP, ← hz, invf z hzl, ← hinv]
    split_ifs with h
    · simp only [Option.bind_some]
      rw [(hsplit (inv - 1) h.2).1, (hsplit (inv - 1) h.2).2]
    · rfl
  rw [hex, hco, hval_eq]
  by_cases h0 : inv = 0
  · have hz0 : s2.regs 210 = 0 := by rw [v210, h0]
    rw [if_neg (by omega)]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_pos hz0]; exact DOut.none_of_SFr hfr.1 hfr.2
    · rw [cost_ifz, if_pos hz0, cost_skip]
      have h3 : ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 100) * κ =
        ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 81) * κ +
          (7 * n + 4) * κ + 15 * κ := by ring
      rw [h3]
      have := Nat.zero_le (((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 81) * κ)
      omega
  · have hz0 : s2.regs 210 ≠ 0 := by rw [v210]; exact h0
    have hc2 := hc.of_SFr hfr.1
    have hw2 : WordAt s2 (dC0 t).a0 0 w := hw.congr (fun i _ => hfr.1.2.1 _ _ (Or.inr (by simp [dC0])))
    obtain ⟨D1, D2⟩ := pC2_spec inp B H s2 hc2 w hw2 hwl inv v210 (by omega)
    have D2' : (pC2 q t).cost inp B s2 ≤ ((11 * dVb q t n + 11) * P.L + 14 * n +
      7 * P.k + 11 * dVb q t n + 81) * κ + caCost q t n B := D2
    have e : (if inv ≠ 0 ∧ inv - 1 < q ^ P.h then
        vMid t P p (w.take P.m) ((inv - 1) / q ^ P.h₂) ((inv - 1) % q ^ P.h₂) else none) =
        (if inv - 1 < q ^ P.h then
        vMid t P p (w.take P.m) ((inv - 1) / q ^ P.h₂) ((inv - 1) % q ^ P.h₂) else none) := by
      simp [h0]
    rw [e]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_neg hz0]; exact DOut.pre hfr.1 hfr.2 D1
    · rw [cost_ifz, if_neg hz0]
      have h3 : ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 100) * κ =
        ((11 * dVb q t n + 11) * P.L + 14 * n + 7 * P.k + 11 * dVb q t n + 81) * κ +
          (7 * n + 4) * κ + 15 * κ := by ring
      rw [h3]
      omega

end Levels

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamDecode3
/-!
# The decoder, part 3: the enumeration body and the enumeration (q379, Part D)

`pBody q t` is the body run by the scripts enumerator `dC0 t` (depth `t`) on every visited word
`w`: if the done flag (register `2`) is clear and `|w| = n`, it runs the candidate test, which
stores `validate t n p w` (when it is `some`) in array `2` and sets the flag.
`decEnum_spec`: after the enumeration, the flag / array `2` hold
`((scripts t z).map Prod.snd).findSome? (validate t n p)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem validate_some_length {q : ℕ} (hq : 0 < q) (t n p : ℕ) (c r : Word q)
    (h : validate t n p c = some r) : r.length = (parameters q t n).k := by
  by_cases hc : c.length = n
  · rw [validate_unfold t n p c hc] at h
    have hmk := dec_m_le_k q t n
    have hmn := params_m_le q t n
    rcases hs : shortInverse t (parameters q t n).h (c.drop (parameters q t n).m) with _ | s
    · rw [hs] at h; simp at h
    · rw [hs] at h
      simp only [Option.bind_some, vMid, vTail] at h
      split_ifs at h
      simp only [Option.some.injEq] at h
      rw [← h, List.length_append, dec_repr_length hq, List.length_take]
      omega
  · rw [validate_len t n p c hc] at h; simp at h

theorem DCtx.of_regs {q t n p : ℕ} {st st' : HS} (h : DCtx q t n p st)
    (hR : ∀ r, ((r < 200 ∧ r ≠ 2) ∨ r = 400 ∨ r = 403 ∨ r = 418 ∨ r = 424) → st'.regs r = st.regs r)
    (hA : ∀ i, st'.arr 1 i = st.arr 1 i) (hI : ∀ i, st'.arr (dINV t) i = st.arr (dINV t) i) :
    DCtx q t n p st' := by
  have R : ∀ r, r < 200 → r ≠ 2 → st'.regs r = st.regs r := fun r h1 h2 => hR r (Or.inl ⟨h1, h2⟩)
  obtain ⟨h0, h1, h3, h4, ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16⟩,
    g0, g3, g18, g24, prt, inv, invb⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [R _ (by omega) (by omega)]; assumption)
    | (rw [hR _ (by omega)]; assumption)
    | skip
  · intro i hi; rw [hA]; exact prt i hi
  · intro z hz; simp only [hI]; exact inv z hz
  · intro u hu; rw [hI]; exact invb u hu

theorem DInv.stable {q t n p : ℕ} {a : Option (Word q)} {st st' : HS} (h : DInv q t n p a st)
    (hA : (dC0 t).Agree t st st') : DInv q t n p a st' := by
  have nR : ∀ r, r < 510 + 12 * t → ¬ (dC0 t).ownsReg t r := fun r hr hh => by
    simp only [EnumCfg.ownsReg, dC0] at hh; omega
  have nA : ∀ y, (y < 14 + 4 * t ∨ 16 + 5 * t ≤ y) → ¬ (dC0 t).ownsArr t y := fun y hy hh => by
    simp only [EnumCfg.ownsArr, dC0] at hh; omega
  obtain ⟨hc, ho, hd⟩ := h
  refine ⟨hc.of_regs (fun r hr => hA.1 r (nR r (by omega))) (fun i => hA.2.1 _ i (nA 1 (by omega)))
    (fun i => hA.2.1 _ i (nA _ (by unfold dINV; omega))), hA.2.2.2.trans ho, ?_⟩
  have e2 : st'.regs 2 = st.regs 2 := hA.1 2 (nR 2 (by omega))
  rcases hd with ⟨h1, h2⟩ | ⟨r, h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, by rw [e2, h2]⟩
  · exact Or.inr ⟨r, h1, by rw [e2, h2], h3.congr (fun i _ => hA.2.1 _ _ (nA 2 (by omega))), h4⟩

section Body
variable (inp : ℕ → ℕ) (B : ℕ)

theorem pIn_spec {q t n p : ℕ} (H : DHyp q t n p) (hsplit : SplitOK q t n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hVL : st.regs (510 + 12 * t) = w.length) (hwl : w.length ≤ n + 2 * t) :
    DOut t st ((pIn q t).exec inp st) (validate t n p w) ∧
    (pIn q t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 21 * n +
      7 * (parameters q t n).k + 11 * dVb q t n + 105) * kappa B (RAM.bits (DM q t n)) + caCost q t n B := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have hn0 : st.regs 0 = n := hc.n0
  set A := seqs [ar .sub 262 (510 + 12 * t) 0, ar .sub 263 0 (510 + 12 * t), ar .add 262 262 263] with hA
  set s1 := A.exec inp st with hs1
  have hfr := sfr_of_block inp t A (by
      intro r hr; simp only [hA, seqs, Cmd.wregs, ar, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.nil_append, List.append_nil] at hr; omega)
    rfl rfl rfl st
  have v262 : s1.regs 262 = (w.length - n) + (n - w.length) := by
    simp (disch := omega) [hs1, hA, upd_ne, hVL, hn0]
  have c1 : A.cost inp B st ≤ 3 * κ := by
    simp (disch := omega) only [hA, cost_seqs_cons, cost_seqs_nil, cost_ar, exec_seqs_cons,
      exec_ar, HS.setR_regs, upd_ne, upd_eq, hVL, hn0, arith_sub, arith_add]
    have := kb (w.length + n) (by omega)
    have := kb (n + w.length) (by omega)
    have := kb (w.length - n + (n - w.length)) (by omega)
    omega
  have hex : (pIn q t).exec inp st = (Cmd.ifz 262 (pCand q t) .skip).exec inp s1 := rfl
  have hco : (pIn q t).cost inp B st = A.cost inp B st + (Cmd.ifz 262 (pCand q t) .skip).cost inp B s1 := rfl
  have hk := kb (s1.regs 262) (by rw [v262]; omega)
  rw [hex, hco]
  by_cases hn : w.length = n
  · have hz : s1.regs 262 = 0 := by rw [v262]; omega
    have hc1 := hc.of_SFr hfr.1
    have hw1 : WordAt s1 (dC0 t).a0 0 w := hw.congr (fun i _ => hfr.1.2.1 _ _ (Or.inr (by simp [dC0])))
    obtain ⟨D1, D2⟩ := pCand_spec inp B H hsplit s1 hc1 w hw1 hn
    have D2' : (pCand q t).cost inp B s1 ≤ ((11 * dVb q t n + 11) * P.L + 21 * n +
      7 * P.k + 11 * dVb q t n + 100) * κ + caCost q t n B := D2
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_pos hz]; exact DOut.pre hfr.1 hfr.2 D1
    · rw [cost_ifz, if_pos hz]
      have h3 : ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 105) * κ =
        ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 100) * κ + 5 * κ := by ring
      rw [h3]; omega
  · have hz : s1.regs 262 ≠ 0 := by rw [v262]; omega
    rw [validate_len t n p w hn]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_neg hz]; exact DOut.none_of_SFr hfr.1 hfr.2
    · rw [cost_ifz, if_neg hz, cost_skip]
      have h3 : ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 105) * κ =
        ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 100) * κ + 5 * κ := by ring
      rw [h3]
      have := Nat.zero_le (((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 100) * κ)
      omega

theorem pBody_spec {q t n p : ℕ} (H : DHyp q t n p) (hsplit : SplitOK q t n)
    (a : Option (Word q)) (st : HS) (hI : DInv q t n p a st) (w : Word q)
    (hw : WordAt st (dC0 t).a0 0 w)
    (hVL : st.regs (510 + 12 * t) = w.length) (hwl : w.length ≤ n + 2 * t) :
    DInv q t n p (a.or (validate t n p w)) ((pBody q t).exec inp st) ∧
    (dC0 t).BodyFrame t st ((pBody q t).exec inp st) ∧
    (pBody q t).cost inp B st ≤ dBodyCost q t n B := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have hBC : dBodyCost q t n B = ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k +
    11 * dVb q t n + 110) * κ + caCost q t n B := rfl
  obtain ⟨hc, ho, hd⟩ := hI
  have bf : ∀ st', SFr t st st' → (dC0 t).BodyFrame t st st' := fun st' h =>
    ⟨fun r hr _ => h.1 r (by simp only [EnumCfg.ownsReg, dC0] at hr; unfold KeptR; omega),
     fun y i hy _ => h.2.1 y i (by simp only [EnumCfg.ownsArr, dC0] at hy; unfold KeptA; omega)⟩
  rcases hd with ⟨ha, h2⟩ | ⟨r, ha, h2, h3, h4⟩
  · -- not done: run the test
    subst ha
    obtain ⟨⟨D1, D2, D3⟩, C⟩ := pIn_spec inp B H hsplit st hc w hw hVL hwl
    have hex : (pBody q t).exec inp st = (pIn q t).exec inp st := by
      show (Cmd.ifz 2 _ _).exec inp st = _; rw [exec_ifz, if_pos h2]
    rw [hex, Option.none_or]
    refine ⟨⟨hc.of_SFr D1, D1.2.2.2.trans ho, ?_⟩, bf _ D1, ?_⟩
    · rcases hv : validate t n p w with _ | r
      · exact Or.inl ⟨rfl, by rw [D2 hv, h2]⟩
      · obtain ⟨e1, e2⟩ := D3 r hv
        exact Or.inr ⟨r, rfl, e1, e2, validate_some_length (by have := H.hq; omega) t n p w r hv⟩
    · show (Cmd.ifz 2 _ _).cost inp B st ≤ _
      rw [cost_ifz, if_pos h2, h2, hBC]
      have C' : (pIn q t).cost inp B st ≤ ((11 * dVb q t n + 11) * P.L + 21 * n +
        7 * P.k + 11 * dVb q t n + 105) * κ + caCost q t n B := C
      have := kb 0 (by omega)
      have h3 : ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 110) * κ =
        ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 105) * κ + 5 * κ := by ring
      rw [h3]; omega
  · -- done: skip
    subst ha
    have hz : st.regs 2 ≠ 0 := by rw [h2]; omega
    have hex : (pBody q t).exec inp st = st := by
      show (Cmd.ifz 2 _ _).exec inp st = _; rw [exec_ifz, if_neg hz]; rfl
    rw [hex, Option.some_or]
    refine ⟨⟨hc, ho, Or.inr ⟨r, rfl, h2, h3, h4⟩⟩, bf _ (SFr.refl t st), ?_⟩
    show (Cmd.ifz 2 _ _).cost inp B st ≤ _
    rw [cost_ifz, if_neg hz, cost_skip, h2, hBC]
    have := kb 1 (by omega)
    have h3 : ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 110) * κ =
      ((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 109) * κ + κ := by ring
    rw [h3]
    have := Nat.zero_le (((11 * dVb q t n + 11) * P.L + 21 * n + 7 * P.k + 11 * dVb q t n + 109) * κ)
    omega

/-- **The enumeration of the decoder.** -/
theorem decEnum_spec_oai {q t n p : ℕ} (H : DHyp q t n p) (hsplit : SplitOK q t n)
    (z : Word q) (hzl : z.length ≤ n + t) (st : HS) (hI : DInv q t n p none st)
    (hlen : st.regs ((dC0 t).lenR t) = z.length) (hz : WordAt st ((dC0 t).buf t) 0 z) :
    DInv q t n p (((scripts t z).map Prod.snd).findSome? (validate t n p))
      ((enumScripts q t (dC0 t) (pBody q t)).exec inp st) ∧
    (enumScripts q t (dC0 t) (pBody q t)).cost inp B st ≤
      (visits t z).length * (dBodyCost q t n B + (dC0 t).enumE B q z.length t) := by
  have E := enumScripts_spec t (dC0 t) (pBody q t) inp B (DInv q t n p)
    (fun a w => a.or (validate t n p w)) (dBodyCost q t n B) z none
    (fun a st st' h hA => h.stable hA)
    (by
      intro a st1 w j hj hw _ hI1 hVL hvis
      have hwm : w ∈ visits t z := hw ▸ List.getElem_mem hj
      have hwl := length_le_of_mem_visits t z hwm
      exact pBody_spec inp B H hsplit a st1 hI1 w hvis hVL (by omega))
    st hlen hz hI
  obtain ⟨E1, -, -, E4⟩ := E
  refine ⟨?_, E4⟩
  rw [dec_foldl_or_eq_findSome] at E1
  exact E1

end Body

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.decEnum_spec_oai := @EditMulticoloring.Dev.Ram.decEnum_spec_oai
