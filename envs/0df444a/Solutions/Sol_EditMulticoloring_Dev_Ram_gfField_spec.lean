-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.gfField_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:50.963623+00:00
-- url     : https://prove2.me/submissions/8b1d0c54-401a-47fd-b4ea-35e4a7264388

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_gfRem_spec
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

theorem foldl_range_stable {α : Type*} (g : α → ℕ → α) (z : α) (n : ℕ)
    (h : ∀ i, n ≤ i → ∀ y, g y i = y) : ∀ m, n ≤ m →
    (List.range m).foldl g z = (List.range n).foldl g z := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show n + (d + 1) = (n + d) + 1 by omega, List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h _ (by omega), ih (by omega)]

theorem lt_two_pow_min {b N : ℕ} (hb : b < 2 ^ N) : b < 2 ^ (min N (b.log2 + 1)) := by
  rcases le_total N (b.log2 + 1) with h | h
  · rw [min_eq_left h]; exact hb
  · rw [min_eq_right h]; exact Nat.lt_log2_self

theorem testBit_false_of_lt_pow {b n i : ℕ} (hb : b < 2 ^ n) (hi : n ≤ i) : b.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))

theorem binaryMul_fold (a b N : ℕ) (hb : b < 2 ^ N) :
    binaryMul a b = (List.range N).foldl (mulStep b a) 0 := by
  have hn := lt_two_pow_min hb
  have hst : ∀ i, min N (b.log2 + 1) ≤ i → ∀ y, mulStep b a y i = y := by
    intro i hi y; simp [mulStep, testBit_false_of_lt_pow hn hi]
  have e1 := foldl_range_stable (mulStep b a) 0 _ hst N (min_le_left _ _)
  have e2 := foldl_range_stable (mulStep b a) 0 _ hst (b.log2 + 1) (min_le_right _ _)
  rw [e1, ← e2]; rfl

theorem mulStep_lt (b a z i m : ℕ) (hz : z < 2 ^ m) (ha : a * 2 ^ i < 2 ^ m) :
    mulStep b a z i < 2 ^ m := by
  unfold mulStep; split_ifs
  · exact Nat.xor_lt_two_pow hz ha
  · exact hz

theorem binaryMul_lt (a b m n : ℕ) (ha : a < 2 ^ m) (hb : b < 2 ^ n) :
    binaryMul a b < 2 ^ (m + n) := by
  rw [binaryMul_fold a b n hb]
  have : ∀ k ≤ n, (List.range k).foldl (mulStep b a) 0 < 2 ^ (m + n) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      apply mulStep_lt _ _ _ _ _ (ih (by omega))
      calc a * 2 ^ k < 2 ^ m * 2 ^ k := Nat.mul_lt_mul_of_pos_right ha (by positivity)
        _ = 2 ^ (m + k) := by rw [pow_add]
        _ ≤ 2 ^ (m + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact this n le_rfl


theorem mulStep_eq (b a z k : ℕ) :
    mulStep b a z k = if b / 2 ^ k % 2 = 0 then z else Nat.xor z (a * 2 ^ k) := by
  unfold mulStep
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_two_eq_zero_or_one (b / 2 ^ k)
  by_cases h : b / 2 ^ k % 2 = 0 <;> simp [h] <;> omega

/-! ## `gfMul` -/

section Prog
variable (inp : ℕ → ℕ) (B : ℕ)

theorem gfMul_spec (g : ℕ) (s : HS) (M : ℕ)
    (hX : s.regs (g + 6) < 2 ^ s.regs (g + 3)) (hY : s.regs (g + 7) < 2 ^ s.regs (g + 3))
    (hM : 4 * 2 ^ (2 * s.regs (g + 3)) ≤ M) :
    ((gfMul g).exec inp s).regs (g + 8) = binaryMul (s.regs (g + 6)) (s.regs (g + 7)) ∧
    (∀ r', (r' < g + 8 ∨ g + 15 ≤ r') → ((gfMul g).exec inp s).regs r' = s.regs r') ∧
    ((gfMul g).exec inp s).mem = s.mem ∧
    ((gfMul g).exec inp s).cur = s.cur ∧
    ((gfMul g).exec inp s).out = s.out ∧
    (gfMul g).cost inp B s ≤ (8 * s.regs (g + 3) + 8) * kappa B (RAM.bits M) := by
  set W := s.regs (g + 3) with hW
  set a := s.regs (g + 6) with ha
  set b := s.regs (g + 7) with hb
  set PN := 2 ^ (2 * W) with hPN
  have hWW : 2 ^ W * 2 ^ W = PN := by rw [hPN, ← pow_add]; congr 1; omega
  have hWP : 2 ^ W ≤ PN := by
    rw [← hWW]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hW1 : W < 2 ^ W := Nat.lt_two_pow_self
  set s1 := (seqs [lit (g + 8) 0, cp (g + 9) (g + 6), cp (g + 10) (g + 7), lit (g + 14) 2]).exec
    inp s with hs1
  have hn1 : s1.regs (g + 3) = W := by simp (disch := omega) [hs1, upd_ne, hW]
  have K := forLoop_spec inp B (g + 11) (g + 3) (g + 13) (seqs [ar .mod (g + 12) (g + 10) (g + 14),
       .ifz (g + 12) .skip (ar .xor (g + 8) (g + 8) (g + 9)),
       ar .add (g + 9) (g + 9) (g + 9), ar .div (g + 10) (g + 10) (g + 14)]) s1
    (by omega) (by omega)
    (fun k st => st.regs (g + 8) = (List.range k).foldl (mulStep b a) 0 ∧
      st.regs (g + 9) = a * 2 ^ k ∧ st.regs (g + 10) = b / 2 ^ k ∧ st.regs (g + 14) = 2 ∧
      (∀ r', (r' < g + 8 ∨ g + 15 ≤ r') → st.regs r' = s.regs r'))
    (fun _ => 5 * kappa B (RAM.bits M))
    ⟨by simp [hs1], by simp (disch := omega) [hs1, upd_ne, ha], by simp (disch := omega) [hs1, upd_ne, hb],
      by simp (disch := omega) [hs1, upd_ne], fun r' h => by simp (disch := omega) [hs1, upd_ne]⟩
    (by
      intro k hk st ⟨hz, hsh, hbb, h2, hr⟩ hj
      rw [hn1] at hk
      have hzlt : (List.range k).foldl (mulStep b a) 0 < PN := by
        have := binaryMul_lt a b W W hX hY
        have hk' : ∀ k' ≤ W, (List.range k').foldl (mulStep b a) 0 < PN := by
          intro k' hk'
          induction k' with
          | zero => simp; positivity
          | succ k' ih =>
            rw [List.range_succ, List.foldl_append]
            simp only [List.foldl_cons, List.foldl_nil]
            rw [hPN]
            apply mulStep_lt _ _ _ _ _ (by rw [← hPN]; exact ih (by omega))
            calc a * 2 ^ k' < 2 ^ W * 2 ^ k' := Nat.mul_lt_mul_of_pos_right hX (by positivity)
              _ ≤ 2 ^ W * 2 ^ W := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
              _ = 2 ^ (2 * W) := hWW
        exact hk' k hk.le
      have hsh1 : a * 2 ^ (k + 1) ≤ a * 2 ^ W :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hsh2 : a * 2 ^ W < PN := by rw [← hWW]; exact Nat.mul_lt_mul_of_pos_right hX (by positivity)
      have hshk : a * 2 ^ k ≤ a * 2 ^ (k + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hbk : b / 2 ^ k ≤ b := Nat.div_le_self _ _
      have hxor : Nat.xor ((List.range k).foldl (mulStep b a) 0) (a * 2 ^ k) < PN :=
        Nat.xor_lt_two_pow hzlt (by omega)
      have hstep : (List.range (k + 1)).foldl (mulStep b a) 0 =
          if b / 2 ^ k % 2 = 0 then (List.range k).foldl (mulStep b a) 0 else
            Nat.xor ((List.range k).foldl (mulStep b a) 0) (a * 2 ^ k) := by
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [mulStep_eq]
      have hdiv : b / 2 ^ k / 2 = b / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
      have hmul : a * 2 ^ k + a * 2 ^ k = a * 2 ^ (k + 1) := by rw [pow_succ]; ring
      have hbit : b / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have e1 := kappa_bits_le B (a := b / 2 ^ k + 2) (M := M) (by omega)
      have e2 := kappa_bits_le B (a := b / 2 ^ k % 2) (M := M) (by omega)
      have e3 := kappa_bits_le B (a := (List.range k).foldl (mulStep b a) 0 + a * 2 ^ k) (M := M)
        (by omega)
      have e4 := kappa_bits_le B (a := a * 2 ^ k + a * 2 ^ k) (M := M) (by omega)
      by_cases hc : b / 2 ^ k % 2 = 0
      · rw [hc] at hstep
        simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_skip,
          arith_mod, arith_add, arith_div, arith_xor, HS.setR_regs, upd_ne, upd_eq, hz, hsh, hbb, h2,
          hc, if_true, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_skip]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hstep]; simp
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hmul]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hdiv]
        · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]
        · intro r' h
          simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
        · rw [hc] at e2; omega
      · rw [if_neg hc] at hstep
        simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_skip,
          arith_mod, arith_add, arith_div, arith_xor, HS.setR_regs, upd_ne, upd_eq, hz, hsh, hbb, h2,
          hc, if_false, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_skip]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hstep]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hmul]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hdiv]
        · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]
        · intro r' h
          simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
        · omega)
  rw [hn1] at K
  obtain ⟨⟨k1, -, -, -, k2⟩, k3⟩ := K
  have hcur : ((gfMul g).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((gfMul g).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  have hmem : ((gfMul g).exec inp s).mem = s.mem := exec_mem_of_stores inp _ rfl s
  have hex : (gfMul g).exec inp s = (forLoop (g + 11) (g + 3) (g + 13)
      (seqs [ar .mod (g + 12) (g + 10) (g + 14),
       .ifz (g + 12) .skip (ar .xor (g + 8) (g + 8) (g + 9)),
       ar .add (g + 9) (g + 9) (g + 9), ar .div (g + 10) (g + 10) (g + 14)])).exec inp s1 := rfl
  refine ⟨?_, ?_, hmem, hcur, hout, ?_⟩
  · rw [hex, k1, binaryMul_fold a b W hY]
  · rw [hex]; exact k2
  · have hc : (gfMul g).cost inp B s =
        (seqs [lit (g + 8) 0, cp (g + 9) (g + 6), cp (g + 10) (g + 7), lit (g + 14) 2]).cost inp B s +
        ((forLoop (g + 11) (g + 3) (g + 13)
      (seqs [ar .mod (g + 12) (g + 10) (g + 14),
       .ifz (g + 12) .skip (ar .xor (g + 8) (g + 8) (g + 9)),
       ar .add (g + 9) (g + 9) (g + 9), ar .div (g + 10) (g + 10) (g + 14)])).cost inp B s1 + 0) := by
      simp only [gfMul, cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, exec_seqs_nil, hs1]; ring
    rw [hc]
    have c0 : (seqs [lit (g + 8) 0, cp (g + 9) (g + 6), cp (g + 10) (g + 7), lit (g + 14) 2]).cost
        inp B s ≤ 4 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons,
        exec_lit, exec_cp, HS.setR_regs, upd_ne, upd_eq, ← ha, ← hb]
      have := kappa_bits_le B (a := 0) (M := M) (by omega)
      have := kappa_bits_le B (a := 2) (M := M) (by have : 1 ≤ PN := Nat.one_le_two_pow; omega)
      have := kappa_bits_le B (a := a) (M := M) (by omega)
      have := kappa_bits_le B (a := b) (M := M) (by omega)
      omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k3
    have := kappa_bits_le B (a := W) (M := M) (by omega)
    nlinarith


/-! ## The field context and `fieldMul` -/

theorem gfField_spec_oai (g : ℕ) (s : HS) (p W M : ℕ) (hctx : GFCtx s g p W) (hp : p ≠ 0)
    (hX : s.regs (g + 6) < 2 ^ W) (hY : s.regs (g + 7) < 2 ^ W)
    (hM : p * 2 ^ (2 * W) + 4 * 2 ^ (2 * W) ≤ M) :
    ((gfField g).exec inp s).regs (g + 8) = fieldMul p (s.regs (g + 6)) (s.regs (g + 7)) ∧
    (∀ r', (r' < g + 8 ∨ g + 16 ≤ r') → ((gfField g).exec inp s).regs r' = s.regs r') ∧
    ((gfField g).exec inp s).mem = s.mem ∧
    ((gfField g).exec inp s).cur = s.cur ∧
    ((gfField g).exec inp s).out = s.out ∧
    (gfField g).cost inp B s ≤ (36 * W + 14) * kappa B (RAM.bits M) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hctx
  rw [← h3] at hX hY
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := gfMul_spec inp B g s M hX hY (by
    rw [h3]; have : 0 ≤ p * 2 ^ (2 * W) := Nat.zero_le _; omega)
  set s1 := (gfMul g).exec inp s with hs1
  have e0 : s1.regs g = p := by rw [m2 _ (by omega), h0]
  have e4 : s1.regs (g + 4) = 2 * W := by rw [m2 _ (by omega), h4]
  have hz : s1.regs (g + 8) < 2 ^ s1.regs (g + 4) := by
    rw [m1, e4, show 2 * W = W + W by ring]; rw [h3] at hX hY
    exact binaryMul_lt _ _ _ _ hX hY
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := gfRem_spec inp B g s1 M (by rw [e0]; exact hp)
    (by rw [m2 _ (by omega), e0, h1]) (by rw [m2 _ (by omega), e0, h2])
    (by rw [m2 _ (by omega), e4, h5]) hz (by rw [e0, e4]; exact hM)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((gfRem g).exec inp s1).regs (g + 8) = _
    rw [r1, e0, m1]; rfl
  · intro r' h
    show ((gfRem g).exec inp s1).regs r' = _
    rw [r2 r' h, m2 r' (by omega)]
  · show ((gfRem g).exec inp s1).mem = _; rw [r3, m3]
  · show ((gfRem g).exec inp s1).cur = _; rw [r4, m4]
  · show ((gfRem g).exec inp s1).out = _; rw [r5, m5]
  · show (gfMul g).cost inp B s + (gfRem g).cost inp B s1 ≤ _
    rw [e4] at r6; rw [h3] at m6
    nlinarith


/-! ## `bitEval` on a digit array -/

end Prog

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.gfField_spec_oai := @EditMulticoloring.Dev.Ram.gfField_spec_oai
