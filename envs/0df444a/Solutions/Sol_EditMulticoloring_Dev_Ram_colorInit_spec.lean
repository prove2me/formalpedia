-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.colorInit_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:40.670057+00:00
-- url     : https://prove2.me/submissions/cd703680-6a24-42b3-af57-aaa9f0be78c4

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

theorem digitsW_spec (r : ℕ) (s : HS) (M : ℕ)
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + s.regs (r + 3) + s.regs (r + 4) ≤ M) :
    (∀ i < s.regs (r + 2), ((digitsW r).exec inp s).arr (s.regs (r + 3)) (s.regs (r + 4) + i) =
      (s.regs r / s.regs (r + 1) ^ i) % s.regs (r + 1)) ∧
    (∀ y i, ¬ (y = s.regs (r + 3) ∧ s.regs (r + 4) ≤ i ∧ i < s.regs (r + 4) + s.regs (r + 2)) →
      ((digitsW r).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < r + 5 ∨ r + 10 ≤ r') → ((digitsW r).exec inp s).regs r' = s.regs r') ∧
    ((digitsW r).exec inp s).cur = s.cur ∧
    ((digitsW r).exec inp s).out = s.out ∧
    (digitsW r).cost inp B s ≤ (7 * s.regs (r + 2) + 4) * kappa B (RAM.bits M) := by
  set v := s.regs r
  set q := s.regs (r + 1)
  set vD := s.regs (r + 3)
  set voff := s.regs (r + 4)
  set s1 := s.setR (r + 5) v with hs1
  have hn1 : s1.regs (r + 2) = s.regs (r + 2) := by simp [hs1]
  have K := forLoop_spec inp B (r + 6) (r + 2) (r + 9) (seqs [ar .add (r + 7) (r + 4) (r + 6),
    ar .mod (r + 8) (r + 5) (r + 1), ast (r + 3) (r + 7) (r + 8), ar .div (r + 5) (r + 5) (r + 1)])
    s1 (by omega) (by omega)
    (fun k st => st.regs (r + 5) = v / q ^ k ∧
      (∀ i < k, st.arr vD (voff + i) = (v / q ^ i) % q) ∧
      (∀ y i, ¬ (y = vD ∧ voff ≤ i ∧ i < voff + k) → st.arr y i = s.arr y i) ∧
      (∀ r', (r' < r + 5 ∨ r + 10 ≤ r') → st.regs r' = s.regs r'))
    (fun _ => 4 * kappa B (RAM.bits M))
    ⟨by simp [hs1], fun i hi => absurd hi (Nat.not_lt_zero _), fun y i _ => by simp [hs1],
      fun r' h => by simp (disch := omega) [hs1, upd_ne]⟩
    (by
      intro k hk st ⟨hw, hc, hy, hr⟩ hj
      rw [hn1] at hk
      have eq : st.regs (r + 1) = q := hr _ (by omega)
      have eD : st.regs (r + 3) = vD := hr _ (by omega)
      have eoff : st.regs (r + 4) = voff := hr _ (by omega)
      have hle : v / q ^ k ≤ v := Nat.div_le_self _ _
      have hmod : v / q ^ k % q ≤ v / q ^ k := Nat.mod_le _ _
      simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ast,
        arith_add, arith_mod, arith_div, HS.setR_regs, HS.store_regs,
        upd_ne, upd_eq, eD, eoff, eq, hj, hw, cost_seqs_cons, cost_seqs_nil, cost_ar,
        cost_ast]
      refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, HS.store_regs]
        rw [Nat.div_div_eq_div_mul, pow_succ]
      · intro i hi
        simp only [HS.setR_arr, HS.store_arr]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [if_neg (by omega)]; exact hc i hi
        · simp
      · intro y i hyi
        simp only [HS.setR_arr, HS.store_arr]
        rw [if_neg (by omega)]; exact hy y i (by omega)
      · intro r' h
        simp (disch := omega) only [upd_ne, HS.setR_regs, HS.store_regs]; exact hr r' h
      · have e1 := kappa_bits_le B (a := voff + k) (M := M) (by omega)
        have e2 := kappa_bits_le B (a := v / q ^ k + q) (M := M) (by omega)
        have e3 := kappa_bits_le B (a := vD + (voff + k) + v / q ^ k % q) (M := M) (by omega)
        omega)
  rw [hn1] at K
  obtain ⟨⟨-, k2, k3, k4⟩, k5⟩ := K
  have hcur : ((digitsW r).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((digitsW r).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  refine ⟨k2, k3, k4, hcur, hout, ?_⟩
  have hc : (digitsW r).cost inp B s = kappa B (RAM.bits v) +
      (forLoop (r + 6) (r + 2) (r + 9) (seqs [ar .add (r + 7) (r + 4) (r + 6),
    ar .mod (r + 8) (r + 5) (r + 1), ast (r + 3) (r + 7) (r + 8), ar .div (r + 5) (r + 5) (r + 1)])).cost
      inp B s1 := rfl
  rw [hc]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k5
  have := kappa_bits_le B (a := s.regs (r + 2)) (M := M) (by omega)
  have := kappa_bits_le B (a := v) (M := M) (by omega)
  nlinarith

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

theorem two_pow_log2_le (p : ℕ) (hp : p ≠ 0) : 2 ^ p.log2 ≤ p := (Nat.le_log2 hp).mp le_rfl

/-! ## `gfMul` -/

section Prog
variable (inp : ℕ → ℕ) (B : ℕ)


/-! ## The field context and `fieldMul` -/

theorem GFCtx.congr {s s' : HS} {g p W : ℕ} (h : GFCtx s g p W)
    (h' : ∀ r, g ≤ r → r < g + 6 → s'.regs r = s.regs r) : GFCtx s' g p W := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨(h' _ le_rfl (by omega)).trans h0, (h' _ (by omega) (by omega)).trans h1,
    (h' _ (by omega) (by omega)).trans h2, (h' _ (by omega) (by omega)).trans h3,
    (h' _ (by omega) (by omega)).trans h4, (h' _ (by omega) (by omega)).trans h5⟩


theorem div_pow_eq_zero_iff (p k : ℕ) (hp : p ≠ 0) : p / 2 ^ k = 0 ↔ p.log2 < k := by
  rw [Nat.div_eq_zero_iff, Nat.log2_lt hp]
  constructor
  · rintro (h | h)
    · exact absurd h (by positivity)
    · exact h
  · exact Or.inr

theorem gfSetup_spec (g : ℕ) (s : HS) (p W M : ℕ) (h0 : s.regs g = p) (h3 : s.regs (g + 3) = W)
    (hp : p ≠ 0) (hpW : p < 2 ^ W) (hM : p * 2 ^ (2 * W) + 4 * 2 ^ (2 * W) ≤ M) :
    GFCtx ((gfSetup g).exec inp s) g p W ∧
    (∀ r', r' ≠ g + 1 → r' ≠ g + 2 → r' ≠ g + 4 → r' ≠ g + 5 → (r' < g + 8 ∨ g + 16 ≤ r') →
      ((gfSetup g).exec inp s).regs r' = s.regs r') ∧
    ((gfSetup g).exec inp s).mem = s.mem ∧
    ((gfSetup g).exec inp s).cur = s.cur ∧
    ((gfSetup g).exec inp s).out = s.out ∧
    (gfSetup g).cost inp B s ≤ (16 * W + 12) * kappa B (RAM.bits M) := by
  set lp := p.log2 with hlp
  have hlpW : lp < W := (Nat.log2_lt hp).mpr hpW
  have hWW : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW1 : W < 2 ^ W := Nat.lt_two_pow_self
  have hP2p : 2 ^ lp ≤ p := two_pow_log2_le p hp
  have hpM : p ≤ p * 2 ^ (2 * W) := Nat.le_mul_of_pos_right _ (by positivity)
  set s1 := (seqs [lit (g + 1) 0, lit (g + 2) 1, cp (g + 9) g, lit (g + 14) 2]).exec inp s with hs1
  have hn1 : s1.regs (g + 3) = W := by simp (disch := omega) [hs1, upd_ne, h3]
  have K := forLoop_spec inp B (g + 11) (g + 3) (g + 13) (seqs [ar .div (g + 9) (g + 9) (g + 14),
      .ifz (g + 9) .skip (seqs [lit (g + 13) 1, ar .add (g + 1) (g + 1) (g + 13),
        ar .add (g + 2) (g + 2) (g + 2)])]) s1 (by omega) (by omega)
    (fun k st => st.regs (g + 9) = p / 2 ^ k ∧ st.regs (g + 1) = min k lp ∧
      st.regs (g + 2) = 2 ^ (min k lp) ∧ st.regs (g + 14) = 2 ∧
      (∀ r', r' ≠ g + 1 → r' ≠ g + 2 → (r' < g + 8 ∨ g + 16 ≤ r') → st.regs r' = s.regs r'))
    (fun _ => 5 * kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [hs1, upd_ne, h0], by simp (disch := omega) [hs1, upd_ne],
      by simp (disch := omega) [hs1, upd_ne], by simp (disch := omega) [hs1, upd_ne],
      fun r' h1 h2 h => by simp (disch := omega) [hs1, upd_ne]⟩
    (by
      intro k hk st ⟨hq, hl, hP, h2, hr⟩ hj
      rw [hn1] at hk
      have hdiv : p / 2 ^ k / 2 = p / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
      have hpk : p / 2 ^ k ≤ p := Nat.div_le_self _ _
      have hmin : 2 ^ (min k lp) ≤ 2 ^ lp := Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
      have K1 := kappa_bits_le B (a := p / 2 ^ k + 2) (M := M) (by omega)
      have K2 := kappa_bits_le B (a := p / 2 ^ (k + 1)) (M := M) (by
        have := Nat.div_le_self p (2 ^ (k + 1)); omega)
      have K3 := kappa_bits_le B (a := 1) (M := M) (by omega)
      have K4 := kappa_bits_le B (a := min k lp + 1) (M := M) (by
        have := min_le_right k lp; omega)
      have K5 := kappa_bits_le B (a := 2 ^ (min k lp) + 2 ^ (min k lp)) (M := M) (by omega)
      by_cases hc : p / 2 ^ (k + 1) = 0
      · have hlk : lp < k + 1 := (div_pow_eq_zero_iff p (k + 1) hp).mp hc
        have hm : min (k + 1) lp = min k lp := by omega
        simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_skip,
          exec_lit, arith_add, arith_div, HS.setR_regs, upd_ne, upd_eq, hq, hl, hP, h2, hdiv, hc,
          if_true, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_skip, cost_lit]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); (try rw [hc])
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hm]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hm]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs])
        · intro r' h1 h2 h
          simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h1 h2 h
        · rw [hc] at K2; omega
      · have hlk : k + 1 ≤ lp := by
          have := (div_pow_eq_zero_iff p (k + 1) hp).not.mp hc; omega
        have hm : min (k + 1) lp = min k lp + 1 := by omega
        have hm2 : 2 ^ (min k lp) + 2 ^ (min k lp) = 2 ^ (min (k + 1) lp) := by
          rw [hm, pow_succ]; ring
        simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_skip,
          exec_lit, arith_add, arith_div, HS.setR_regs, upd_ne, upd_eq, hq, hl, hP, h2, hdiv, hc,
          if_false, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_skip, cost_lit]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs])
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hm]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hm2]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs])
        · intro r' h1 h2 h
          simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h1 h2 h
        · omega)
  rw [hn1] at K
  obtain ⟨⟨-, k1, k2, -, k4⟩, k5⟩ := K
  set s2 := (forLoop (g + 11) (g + 3) (g + 13) (seqs [ar .div (g + 9) (g + 9) (g + 14),
      .ifz (g + 9) .skip (seqs [lit (g + 13) 1, ar .add (g + 1) (g + 1) (g + 13),
        ar .add (g + 2) (g + 2) (g + 2)])])).exec inp s1 with hs2
  set s3 := (seqs [ar .add (g + 4) (g + 3) (g + 3), lit (g + 5) 1]).exec inp s2 with hs3
  have e3 : s2.regs (g + 3) = W := by rw [k4 _ (by omega) (by omega) (by omega), h3]
  have f4 : s3.regs (g + 4) = 2 * W := by simp (disch := omega) [hs3, upd_ne, e3]; ring
  have K' := forLoop_spec inp B (g + 11) (g + 4) (g + 13) (ar .add (g + 5) (g + 5) (g + 5)) s3
    (by omega) (by omega)
    (fun k st => st.regs (g + 5) = 2 ^ k ∧
      (∀ r', r' ≠ g + 5 → (r' < g + 8 ∨ g + 16 ≤ r') → st.regs r' = s3.regs r'))
    (fun _ => kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [hs3, upd_ne], fun r' h1 h => by simp (disch := omega) [upd_ne]⟩
    (by
      intro k hk st ⟨h5, hr⟩ hj
      rw [f4] at hk
      have : 2 ^ (k + 1) ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have K1 := kappa_bits_le B (a := 2 ^ k + 2 ^ k) (M := M) (by rw [pow_succ] at this; omega)
      simp (disch := omega) only [exec_ar, arith_add, HS.setR_regs, upd_ne, upd_eq, h5, cost_ar]
      refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_⟩, K1⟩
      · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [pow_succ]; ring
      · intro r' h1 h
        simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h1 h)
  rw [f4] at K'
  obtain ⟨⟨k6, k7⟩, k8⟩ := K'
  have hex : (gfSetup g).exec inp s = (forLoop (g + 11) (g + 4) (g + 13)
      (ar .add (g + 5) (g + 5) (g + 5))).exec inp s3 := rfl
  have fr3 : ∀ r', r' ≠ g + 4 → r' ≠ g + 5 → s3.regs r' = s2.regs r' := by
    intro r' h1 h2; simp (disch := omega) [hs3, upd_ne]
  have hcur : ((gfSetup g).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((gfSetup g).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  have hmem : ((gfSetup g).exec inp s).mem = s.mem := exec_mem_of_stores inp _ rfl s
  have hmin : min W lp = lp := by omega
  rw [hex]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hex ▸ hmem, hex ▸ hcur, hex ▸ hout, ?_⟩
  · rw [k7 _ (by omega) (by omega), fr3 _ (by omega) (by omega), k4 _ (by omega) (by omega) (by omega),
      h0]
  · rw [k7 _ (by omega) (by omega), fr3 _ (by omega) (by omega), k1, hmin]
  · rw [k7 _ (by omega) (by omega), fr3 _ (by omega) (by omega), k2, hmin]
  · rw [k7 _ (by omega) (by omega), fr3 _ (by omega) (by omega), e3]
  · rw [k7 _ (by omega) (by omega), f4]
  · rw [k6]
  · intro r' a1 a2 a4 a5 h
    rw [k7 _ a5 h, fr3 _ a4 a5, k4 _ a1 a2 h]
  · have hc : (gfSetup g).cost inp B s =
        (seqs [lit (g + 1) 0, lit (g + 2) 1, cp (g + 9) g, lit (g + 14) 2]).cost inp B s +
        ((forLoop (g + 11) (g + 3) (g + 13) (seqs [ar .div (g + 9) (g + 9) (g + 14),
      .ifz (g + 9) .skip (seqs [lit (g + 13) 1, ar .add (g + 1) (g + 1) (g + 13),
        ar .add (g + 2) (g + 2) (g + 2)])])).cost inp B s1 +
        ((seqs [ar .add (g + 4) (g + 3) (g + 3), lit (g + 5) 1]).cost inp B s2 +
        ((forLoop (g + 11) (g + 4) (g + 13) (ar .add (g + 5) (g + 5) (g + 5))).cost inp B s3 + 0))) := by
      simp only [gfSetup, cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, exec_seqs_nil, hs1, hs2, hs3]; ring
    rw [hc]
    have c0 : (seqs [lit (g + 1) 0, lit (g + 2) 1, cp (g + 9) g, lit (g + 14) 2]).cost
        inp B s ≤ 4 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons,
        exec_lit, exec_cp, HS.setR_regs, upd_ne, upd_eq, h0]
      have := kappa_bits_le B (a := 0) (M := M) (by omega)
      have := kappa_bits_le B (a := 1) (M := M) (by omega)
      have := kappa_bits_le B (a := 2) (M := M) (by have : 1 ≤ 2 ^ W := Nat.one_le_two_pow; omega)
      have := kappa_bits_le B (a := p) (M := M) (by omega)
      omega
    have c1 : (seqs [ar .add (g + 4) (g + 3) (g + 3), lit (g + 5) 1]).cost inp B s2 ≤
        2 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_seqs_cons,
        exec_lit, exec_ar, HS.setR_regs, upd_ne, upd_eq, e3]
      have := kappa_bits_le B (a := W + W) (M := M) (by omega)
      have := kappa_bits_le B (a := 1) (M := M) (by omega)
      omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k5 k8
    have := kappa_bits_le B (a := W) (M := M) (by omega)
    have := kappa_bits_le B (a := 2 * W) (M := M) (by
      have : 2 * W < 2 ^ (2 * W) := Nat.lt_two_pow_self; omega)
    nlinarith


/-! ## `bitEval` on a digit array -/

end Prog

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

theorem value_le {q : ℕ} (x : Word q) : value x ≤ q ^ x.length := by
  rcases value_lt x with h | rfl
  · exact h.le
  · simp [value]

theorem colorInit_spec_oai {q : ℕ} (s : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) (x : Word q) (st : HS)
    (p W Q K Ms Mb : ℕ)
    (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
    (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
    (h24 : st.regs (g + 24) = Q)
    (hlen : st.regs (cfg.lenR s) = x.length) (hx : WordAt st (cfg.buf s) 0 x)
    (hp : p ≠ 0) (hpW : p < 2 ^ W)
    (hMs : p * 2 ^ (2 * W) + 4 * 2 ^ (2 * W) ≤ Ms)
    (hMb : q ^ x.length + 2 * q + cfg.a0 + s + XA + DG + 2 * x.length + Q + K + 2 ≤ Mb) :
    let st' := (colorInit q s cfg g XA DG).exec inp st
    GFCtx st' g p W ∧ st'.regs (g + 18) = K ∧ st'.regs (g + 24) = Q ∧
    st'.regs (g + 25) = x.length ∧ WordAt st' XA 0 x ∧
    (∀ i < K, st'.arr DG i = (value x / Q ^ i) % Q) ∧
    (∀ r, (r < g ∨ g + 51 ≤ r) → st'.regs r = st.regs r) ∧
    (∀ y i, y ≠ XA → y ≠ DG → st'.arr y i = st.arr y i) ∧
    st'.cur = st.cur ∧ st'.out = st.out ∧
    (colorInit q s cfg g XA DG).cost inp B st ≤
      (16 * W + 12) * kappa B (RAM.bits Ms) + (14 * x.length + 7 * K + 26) * kappa B (RAM.bits Mb) := by
  intro st'
  have hbuf : cfg.buf s = cfg.a0 + 1 + s := rfl
  have hlenR : cfg.lenR s = cfg.r0 + (18 + 3 * s) := rfl
  -- phase 1: field context
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := gfSetup_spec inp B g st p W Ms h0 h3 hp hpW hMs
  set s1 := (gfSetup g).exec inp st with hs1
  have r1 : ∀ r, (r < g ∨ g + 16 ≤ r) → s1.regs r = st.regs r := fun r h => a2 r (by omega)
    (by omega) (by omega) (by omega) (by omega)
  -- phase 2
  set P2 := seqs [lit (g + 40) (cfg.buf s), lit (g + 41) 0, lit (g + 42) XA, lit (g + 43) 0,
      cp (g + 44) (cfg.lenR s), cp (g + 25) (cfg.lenR s)] with hP2
  set s2 := P2.exec inp s1 with hs2
  have r2 : ∀ r, r ≠ g + 25 → (r < g + 40 ∨ g + 45 ≤ r) → s2.regs r = s1.regs r := by
    intro r h1 h2; simp (disch := omega) [hs2, hP2, upd_ne]
  have m2 : s2.mem = s1.mem := by simp [hs2, hP2]
  have L1 : s1.regs (cfg.lenR s) = x.length := by rw [r1 _ (by omega), hlen]
  have v40 : s2.regs (g + 40) = cfg.buf s := by simp (disch := omega) [hs2, hP2, upd_ne]
  have v41 : s2.regs (g + 41) = 0 := by simp (disch := omega) [hs2, hP2, upd_ne]
  have v42 : s2.regs (g + 42) = XA := by simp (disch := omega) [hs2, hP2, upd_ne]
  have v43 : s2.regs (g + 43) = 0 := by simp (disch := omega) [hs2, hP2, upd_ne]
  have v44 : s2.regs (g + 44) = x.length := by
    simp (disch := omega) [hs2, hP2, upd_ne]; exact L1
  have v25 : s2.regs (g + 25) = x.length := by
    simp (disch := omega) [hs2, hP2, upd_ne]; exact L1
  have c2 : P2.cost inp B s1 ≤ 6 * kappa B (RAM.bits Mb) := by
    simp (disch := omega) only [hP2, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_lit, exec_cp, HS.setR_regs, upd_ne, upd_eq]
    rw [L1]
    have := kappa_bits_le B (a := cfg.buf s) (M := Mb) (by omega)
    have := kappa_bits_le B (a := 0) (M := Mb) (by omega)
    have := kappa_bits_le B (a := XA) (M := Mb) (by omega)
    have := kappa_bits_le B (a := x.length) (M := Mb) (by omega)
    omega
  -- phase 3: copy x to XA
  have hx2 : WordAt s2 (cfg.buf s) 0 x := hx.congr (fun i _ => by
    simp only [HS.arr]; rw [m2, a3])
  have hnd : [g + 40, g + 41, g + 42, g + 43, g + 44, g + 45, g + 46, g + 47, g + 48].Nodup := by
    simp
  have hSD : s2.regs (g + 40) ≠ s2.regs (g + 42) := by rw [v40, v42, hbuf]; omega
  have hMc : s2.regs (g + 40) + s2.regs (g + 41) + s2.regs (g + 42) + s2.regs (g + 43) +
      s2.regs (g + 44) + q ≤ Mb := by rw [v40, v41, v42, v43, v44, hbuf]; omega
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := copyW_spec inp B (g + 40) (g + 41) (g + 42) (g + 43) (g + 44)
    (g + 45) (g + 46) (g + 47) (g + 48) s2 hnd hSD q Mb
    (fun i hi => by rw [v40, v41]; rw [v44] at hi; exact (hx2.lt i (by omega)).le) hMc
  have hw3 := copyW_word inp (g + 40) (g + 41) (g + 42) (g + 43) (g + 44) (g + 45) (g + 46) (g + 47)
    (g + 48) s2 x hnd (by rw [v40, v42]; omega) (by rw [v40, v41]; exact hx2) v44
  rw [v42, v43] at hw3 b2
  rw [v44] at b6
  set s3 := (copyW (g + 40) (g + 41) (g + 42) (g + 43) (g + 44) (g + 45) (g + 46) (g + 47) (g + 48)).exec
    inp s2 with hs3
  have r3 : ∀ r, (r < g + 45 ∨ g + 49 ≤ r) → s3.regs r = s2.regs r := fun r h =>
    b3 r (by omega) (by omega) (by omega) (by omega)
  -- phase 4: value of x
  set P4 := seqs [lit (g + 40) XA, lit (g + 41) 0, cp (g + 42) (g + 25), lit (g + 43) q] with hP4
  set s4 := P4.exec inp s3 with hs4
  have r4 : ∀ r, (r < g + 40 ∨ g + 44 ≤ r) → s4.regs r = s3.regs r := by
    intro r h; simp (disch := omega) [hs4, hP4, upd_ne]
  have m4 : s4.mem = s3.mem := by simp [hs4, hP4]
  have u25 : s3.regs (g + 25) = x.length := by rw [r3 _ (by omega), v25]
  have w40 : s4.regs (g + 40) = XA := by simp (disch := omega) [hs4, hP4, upd_ne]
  have w41 : s4.regs (g + 41) = 0 := by simp (disch := omega) [hs4, hP4, upd_ne]
  have w42 : s4.regs (g + 42) = x.length := by simp (disch := omega) [hs4, hP4, upd_ne, u25]
  have w43 : s4.regs (g + 43) = q := by simp (disch := omega) [hs4, hP4, upd_ne]
  have c4 : P4.cost inp B s3 ≤ 4 * kappa B (RAM.bits Mb) := by
    simp (disch := omega) only [hP4, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_lit, exec_cp, HS.setR_regs, upd_ne, upd_eq, u25]
    have := kappa_bits_le B (a := XA) (M := Mb) (by omega)
    have := kappa_bits_le B (a := 0) (M := Mb) (by omega)
    have := kappa_bits_le B (a := q) (M := Mb) (by omega)
    have := kappa_bits_le B (a := x.length) (M := Mb) (by omega)
    omega
  have hw4 : WordAt s4 XA 0 x := hw3.congr (fun i _ => by simp only [HS.arr]; rw [m4])
  have hval := valueW_word inp (g + 40) s4 x (by rw [w40, w41]; exact hw4) w42 w43
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := valueW_spec inp B (g + 40) s4 Mb
    (fun i hi => by rw [w40, w41, w43]; rw [w42] at hi; exact hw4.lt i (by omega))
    (by rw [w40, w41, w42, w43]; omega)
  rw [w42] at d6
  set s5 := (valueW (g + 40)).exec inp s4 with hs5
  -- phase 6: digits
  set P6 := seqs [cp (g + 40) (g + 44), cp (g + 41) (g + 24), cp (g + 42) (g + 18), lit (g + 43) DG,
      lit (g + 44) 0] with hP6
  set s6 := P6.exec inp s5 with hs6
  have r6 : ∀ r, (r < g + 40 ∨ g + 45 ≤ r) → s6.regs r = s5.regs r := by
    intro r h; simp (disch := omega) [hs6, hP6, upd_ne]
  have m6 : s6.mem = s5.mem := by simp [hs6, hP6]
  -- registers below g+40 survive phases 2..5 (except g+25)
  have low : ∀ r, r < g + 40 → s5.regs r = s3.regs r := fun r h => by
    rw [d2 r (by omega), r4 r (by omega)]
  have e24 : s5.regs (g + 24) = Q := by
    rw [low _ (by omega), r3 _ (by omega), r2 _ (by omega) (by omega), r1 _ (by omega), h24]
  have e18 : s5.regs (g + 18) = K := by
    rw [low _ (by omega), r3 _ (by omega), r2 _ (by omega) (by omega), r1 _ (by omega), h18]
  have hvx : value x ≤ q ^ x.length := value_le x
  have x40 : s6.regs (g + 40) = value x := by simp (disch := omega) [hs6, hP6, upd_ne]; exact hval
  have x41 : s6.regs (g + 41) = Q := by simp (disch := omega) [hs6, hP6, upd_ne, e24]
  have x42 : s6.regs (g + 42) = K := by simp (disch := omega) [hs6, hP6, upd_ne, e18]
  have x43 : s6.regs (g + 43) = DG := by simp (disch := omega) [hs6, hP6, upd_ne]
  have x44 : s6.regs (g + 44) = 0 := by simp (disch := omega) [hs6, hP6, upd_ne]
  have c6 : P6.cost inp B s5 ≤ 5 * kappa B (RAM.bits Mb) := by
    simp (disch := omega) only [hP6, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_lit, exec_cp, HS.setR_regs, upd_ne, upd_eq, e24, e18]
    rw [hval]
    have := kappa_bits_le B (a := value x) (M := Mb) (by omega)
    have := kappa_bits_le B (a := 0) (M := Mb) (by omega)
    have := kappa_bits_le B (a := Q) (M := Mb) (by omega)
    have := kappa_bits_le B (a := K) (M := Mb) (by omega)
    have := kappa_bits_le B (a := DG) (M := Mb) (by omega)
    omega
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := digitsW_spec inp B (g + 40) s6 Mb
    (by rw [x40, x41, x42, x43, x44]; omega)
  simp only [x40, x41, x42, x43, x44] at f1 f2
  rw [x42] at f6
  have hex : st' = (digitsW (g + 40)).exec inp s6 := rfl
  have hmem5 : ∀ y i, y ≠ XA → s5.arr y i = st.arr y i := by
    intro y i hy
    simp only [HS.arr]; rw [d3, m4]
    show s3.arr y i = st.arr y i
    rw [b2 y i (by omega)]; simp only [HS.arr]; rw [m2, a3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hex]
    refine a1.congr (fun r h1 h2 => ?_)
    rw [f3 r (by omega), r6 r (by omega), low r (by omega), r3 r (by omega),
      r2 r (by omega) (by omega)]
  · rw [hex, f3 _ (by omega), r6 _ (by omega), e18]
  · rw [hex, f3 _ (by omega), r6 _ (by omega), e24]
  · rw [hex, f3 _ (by omega), r6 _ (by omega), low _ (by omega), u25]
  · rw [hex]
    refine hw4.congr (fun i _ => ?_)
    rw [f2 _ _ (by omega)]
    simp only [HS.arr]; rw [m6, d3]
  · intro i hi; rw [hex]; have := f1 i hi; simpa using this
  · intro r h
    rw [hex, f3 r (by omega), r6 r (by omega), d2 r (by omega), r4 r (by omega), r3 r (by omega),
      r2 r (by omega) (by omega), r1 r (by omega)]
  · intro y i h1 h2
    rw [hex, f2 _ _ (by omega)]
    simp only [HS.arr]; rw [m6]; exact hmem5 y i h1
  · rw [hex, f4]
    show (P6.exec inp s5).cur = _
    simp only [hs6, hP6, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_cur]
    rw [d4]; show (P4.exec inp s3).cur = _
    simp only [hP4, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_cur]
    rw [b4]; show (P2.exec inp s1).cur = _
    simp only [hP2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_cur]
    exact a4
  · rw [hex, f5]
    show (P6.exec inp s5).out = _
    simp only [hs6, hP6, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_out]
    rw [d5]; show (P4.exec inp s3).out = _
    simp only [hP4, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_out]
    rw [b5]; show (P2.exec inp s1).out = _
    simp only [hP2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_out]
    exact a5
  · have hc : (colorInit q s cfg g XA DG).cost inp B st = (gfSetup g).cost inp B st +
        (P2.cost inp B s1 + ((copyW (g + 40) (g + 41) (g + 42) (g + 43) (g + 44) (g + 45) (g + 46)
          (g + 47) (g + 48)).cost inp B s2 + (P4.cost inp B s3 + ((valueW (g + 40)).cost inp B s4 +
          (P6.cost inp B s5 + ((digitsW (g + 40)).cost inp B s6 + 0)))))) := rfl
    rw [hc]
    have : (14 * x.length + 7 * K + 26) * kappa B (RAM.bits Mb) =
      (7 * x.length + 3) * kappa B (RAM.bits Mb) + (7 * x.length + 4) * kappa B (RAM.bits Mb) +
      (7 * K + 4) * kappa B (RAM.bits Mb) + 15 * kappa B (RAM.bits Mb) := by ring
    omega

end Init

/-! ## Enumeration: digits of every neighbour -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.colorInit_spec_oai := @EditMulticoloring.Dev.Ram.colorInit_spec_oai
