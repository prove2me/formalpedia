-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.modulusW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:23.753356+00:00
-- url     : https://prove2.me/submissions/186d5e14-3f3b-4044-8ec5-768e0fd0b9c0

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

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

theorem upd_ne {f : ℕ → ℕ} {a b v : ℕ} (h : b ≠ a) : Function.update f a v b = f b :=
  Function.update_of_ne h v f
theorem upd_eq {f : ℕ → ℕ} {a b v : ℕ} (h : b = a) : Function.update f a v b = v := by
  subst h; simp

/-! ## `exec` and `cost` of the constructors -/

section ExecCost
variable (inp : ℕ → ℕ) (B : ℕ)

theorem exec_loop (a : ℕ) (c : Cmd) (s : HS) :
    (Cmd.loop a c).exec inp s = (c.exec inp)^[s.regs a] s := rfl

end ExecCost

/-! ## Monotonicity of the charges -/

theorem bits_mono {a b : ℕ} (h : a ≤ b) : RAM.bits a ≤ RAM.bits b := by
  unfold RAM.bits
  have := Nat.log_mono_right (b := 2) h
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  omega

theorem kappa_mono {B B' W W' : ℕ} (hB : B ≤ B') (hW : W ≤ W') : kappa B W ≤ kappa B' W' := by
  unfold kappa
  have : (W + 2) ^ 2 ≤ (W' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem kappa_mono_right (B : ℕ) {W W' : ℕ} (hW : W ≤ W') : kappa B W ≤ kappa B W' :=
  kappa_mono le_rfl hW

/-- The standard way to bound a charge: the data is at most `M`. -/
theorem kappa_bits_le (B : ℕ) {a M : ℕ} (h : a ≤ M) : kappa B (RAM.bits a) ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (bits_mono h)

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

/-! ## `gfMul` -/

section Prog
variable (inp : ℕ → ℕ) (B : ℕ)


theorem remStep_eq (p z i : ℕ) (hp : p ≠ 0) :
    remStep p z i = if i < p.log2 then z else if z / 2 ^ i % 2 = 0 then z else
      Nat.xor z (p * (2 ^ i / 2 ^ p.log2)) := by
  unfold remStep
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_two_eq_zero_or_one (z / 2 ^ i)
  by_cases h1 : i < p.log2
  · rw [if_pos h1, if_neg (by omega)]
  · rw [if_neg h1, Nat.pow_div (by omega) (by norm_num)]
    by_cases h : z / 2 ^ i % 2 = 0
    · rw [if_pos h, if_neg]; simp [h]
    · rw [if_neg h, if_pos]; refine ⟨hp, by omega, ?_⟩; simp; omega

theorem remStep_lt (p z i N : ℕ) (hz : z < 2 ^ N) (hi : i < N) : remStep p z i < 2 ^ N := by
  unfold remStep
  split_ifs with h
  · apply Nat.xor_lt_two_pow hz
    calc p * 2 ^ (i - p.log2) < 2 ^ (p.log2 + 1) * 2 ^ (i - p.log2) :=
          Nat.mul_lt_mul_of_pos_right (p_lt_pow p) (by positivity)
      _ = 2 ^ (i + 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hi
  · exact hz

theorem log2_lt_pow (p : ℕ) : p.log2 < 2 ^ p.log2 := Nat.lt_two_pow_self

theorem gfRem_spec (g : ℕ) (s : HS) (M : ℕ) (hp : s.regs g ≠ 0)
    (hlp : s.regs (g + 1) = (s.regs g).log2) (hP2 : s.regs (g + 2) = 2 ^ (s.regs g).log2)
    (hPN : s.regs (g + 5) = 2 ^ s.regs (g + 4)) (hz : s.regs (g + 8) < 2 ^ s.regs (g + 4))
    (hM : s.regs g * 2 ^ s.regs (g + 4) + 4 * 2 ^ s.regs (g + 4) ≤ M) :
    ((gfRem g).exec inp s).regs (g + 8) = binaryRem (s.regs g) (s.regs (g + 8)) ∧
    (∀ r', (r' < g + 8 ∨ g + 16 ≤ r') → ((gfRem g).exec inp s).regs r' = s.regs r') ∧
    ((gfRem g).exec inp s).mem = s.mem ∧
    ((gfRem g).exec inp s).cur = s.cur ∧
    ((gfRem g).exec inp s).out = s.out ∧
    (gfRem g).cost inp B s ≤ (14 * s.regs (g + 4) + 6) * kappa B (RAM.bits M) := by
  set N := s.regs (g + 4) with hN
  set p := s.regs g with hpd
  set a := s.regs (g + 8) with ha
  set lp := p.log2 with hlpd
  set F := fun z k => remStep p z (N - 1 - k) with hF
  have hN1 : N < 2 ^ N := Nat.lt_two_pow_self
  have hP2p : 2 ^ lp ≤ p := two_pow_log2_le p hp
  have hlp2 : lp < 2 ^ lp := log2_lt_pow p
  have hpN : p ≤ p * 2 ^ N := Nat.le_mul_of_pos_right _ (by positivity)
  set s1 := (seqs [cp (g + 9) (g + 5), cp (g + 10) (g + 4), lit (g + 14) 2]).exec inp s with hs1
  have hn1 : s1.regs (g + 4) = N := by simp (disch := omega) [hs1, upd_ne, hN]
  have K := forLoop_spec inp B (g + 11) (g + 4) (g + 13) (seqs [lit (g + 13) 1,
      ar .sub (g + 10) (g + 10) (g + 13),
      ar .div (g + 9) (g + 9) (g + 14), ar .lt (g + 12) (g + 10) (g + 1),
      .ifz (g + 12) (seqs [ar .div (g + 15) (g + 8) (g + 9), ar .mod (g + 15) (g + 15) (g + 14),
        .ifz (g + 15) .skip (seqs [ar .div (g + 15) (g + 9) (g + 2), ar .mul (g + 15) g (g + 15),
          ar .xor (g + 8) (g + 8) (g + 15)])]) .skip]) s1
    (by omega) (by omega)
    (fun k st => st.regs (g + 8) = (List.range k).foldl F a ∧
      st.regs (g + 9) = 2 ^ (N - k) ∧ st.regs (g + 10) = N - k ∧ st.regs (g + 14) = 2 ∧
      (∀ r', (r' < g + 8 ∨ g + 16 ≤ r') → st.regs r' = s.regs r'))
    (fun _ => 11 * kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [hs1, upd_ne, ha], by simp (disch := omega) [hs1, upd_ne, hPN],
      by simp (disch := omega) [hs1, upd_ne, hN], by simp (disch := omega) [hs1, upd_ne],
      fun r' h => by simp (disch := omega) [hs1, upd_ne]⟩
    (by
      intro k hk st ⟨hz', hpw, hi, h2, hr⟩ hj
      rw [hn1] at hk
      have eg : st.regs g = p := hr g (by omega)
      have eg1 : st.regs (g + 1) = lp := by rw [hr _ (by omega), hlp]
      have eg2 : st.regs (g + 2) = 2 ^ lp := by rw [hr _ (by omega), hP2]
      set z := (List.range k).foldl F a with hzd
      have hzlt : ∀ k' ≤ N, (List.range k').foldl F a < 2 ^ N := by
        intro k' hk'
        induction k' with
        | zero => simpa using hz
        | succ k' ih =>
          rw [List.range_succ, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil, hF]
          exact remStep_lt p _ _ N (ih (by omega)) (by omega)
      have hzN : z < 2 ^ N := hzlt k hk.le
      set i := N - 1 - k with hid
      have hpow : 2 ^ (N - k) / 2 = 2 ^ i := by
        rw [show N - k = i + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      have hiN : 2 ^ i ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hstep : (List.range (k + 1)).foldl F a = remStep p z i := by
        rw [List.range_succ, List.foldl_append]; rfl
      rw [remStep_eq p z i hp] at hstep
      have hNk : N - k - 1 = i := by omega
      have hsmall : ∀ x, x ≤ 2 ^ i → ¬ i < lp → p * (2 ^ i / 2 ^ lp) < 2 ^ N := by
        intro x _ hil
        rw [Nat.pow_div (by omega) (by norm_num)]
        calc p * 2 ^ (i - lp) < 2 ^ (lp + 1) * 2 ^ (i - lp) :=
              Nat.mul_lt_mul_of_pos_right (p_lt_pow p) (by positivity)
          _ = 2 ^ (i + 1) := by rw [← pow_add]; congr 1; omega
          _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hdl : 2 ^ i / 2 ^ lp ≤ 2 ^ N := (Nat.div_le_self _ _).trans hiN
      have K1 := kappa_bits_le B (a := 1) (M := M) (by omega)
      have K2 := kappa_bits_le B (a := N - k + 1) (M := M) (by omega)
      have K3 := kappa_bits_le B (a := 2 ^ (N - k) + 2) (M := M) (by
        have : 2 ^ (N - k) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
      have K4 := kappa_bits_le B (a := i + lp) (M := M) (by omega)
      have K5 := kappa_bits_le B (a := if i < lp then 1 else 0) (M := M) (by split_ifs <;> omega)
      have K6 := kappa_bits_le B (a := z + 2 ^ i) (M := M) (by omega)
      have K7 := kappa_bits_le B (a := z / 2 ^ i + 2) (M := M) (by
        have := Nat.div_le_self z (2 ^ i); omega)
      have K8 := kappa_bits_le B (a := z / 2 ^ i % 2) (M := M) (by
        have := Nat.mod_lt (z / 2 ^ i) (show 2 > 0 by norm_num); omega)
      have K9 := kappa_bits_le B (a := 2 ^ i + 2 ^ lp) (M := M) (by omega)
      have K10 := kappa_bits_le B (a := p + 2 ^ i / 2 ^ lp) (M := M) (by omega)
      by_cases hil : i < lp
      · rw [if_pos hil] at hstep
        simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_skip,
          exec_lit, arith_mod, arith_sub, arith_div, arith_lt, arith_xor, arith_mul, HS.setR_regs,
          upd_ne, upd_eq, hpw, hi, h2, eg, eg1, eg2, hpow, hNk, hil, if_true, if_false, hz',
          one_ne_zero, ↓reduceIte,
          cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_skip, cost_lit]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hstep]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [show N - (k + 1) = i by omega]
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); omega
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs])
        · intro r' h
          simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
        · simp only [if_pos hil] at K5
          omega
      · rw [if_neg hil] at hstep
        have hb2 := Nat.mod_lt (z / 2 ^ i) (show 2 > 0 by norm_num)
        by_cases hb : z / 2 ^ i % 2 = 0
        · rw [if_pos hb] at hstep
          simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_skip,
            exec_lit, arith_mod, arith_sub, arith_div, arith_lt, arith_xor, arith_mul, HS.setR_regs,
            upd_ne, upd_eq, hpw, hi, h2, eg, eg1, eg2, hpow, hNk, hil, if_true, if_false, hz',
            one_ne_zero, ↓reduceIte, hb,
            cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_skip, cost_lit]
          refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hstep]
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [show N - (k + 1) = i by omega]
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); omega
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs])
          · intro r' h
            simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
          · simp only [if_neg hil] at K5
            rw [hb] at K8
            omega
        · rw [if_neg hb] at hstep
          have K11 := kappa_bits_le B (a := z + p * (2 ^ i / 2 ^ lp)) (M := M) (by
            have := hsmall 0 (by omega) hil; omega)
          simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_skip,
            exec_lit, arith_mod, arith_sub, arith_div, arith_lt, arith_xor, arith_mul, HS.setR_regs,
            upd_ne, upd_eq, hpw, hi, h2, eg, eg1, eg2, hpow, hNk, hil, if_true, if_false, hz',
            one_ne_zero, ↓reduceIte, hb,
            cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_skip, cost_lit]
          refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hstep]
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [show N - (k + 1) = i by omega]
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); omega
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs])
          · intro r' h
            simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
          · simp only [if_neg hil] at K5
            skip
            omega
)
  rw [hn1] at K
  obtain ⟨⟨k1, -, -, -, k2⟩, k3⟩ := K
  have hcur : ((gfRem g).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((gfRem g).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  have hmem : ((gfRem g).exec inp s).mem = s.mem := exec_mem_of_stores inp _ rfl s
  have hex : (gfRem g).exec inp s = (forLoop (g + 11) (g + 4) (g + 13) (seqs [lit (g + 13) 1, ar .sub (g + 10) (g + 10) (g + 13),
      ar .div (g + 9) (g + 9) (g + 14), ar .lt (g + 12) (g + 10) (g + 1),
      .ifz (g + 12) (seqs [ar .div (g + 15) (g + 8) (g + 9), ar .mod (g + 15) (g + 15) (g + 14),
        .ifz (g + 15) .skip (seqs [ar .div (g + 15) (g + 9) (g + 2), ar .mul (g + 15) g (g + 15),
          ar .xor (g + 8) (g + 8) (g + 15)])]) .skip])).exec inp s1 := rfl
  refine ⟨?_, ?_, hmem, hcur, hout, ?_⟩
  · rw [hex, k1, binaryRem_fold p a N hz]
  · rw [hex]; exact k2
  · have hc : (gfRem g).cost inp B s =
        (seqs [cp (g + 9) (g + 5), cp (g + 10) (g + 4), lit (g + 14) 2]).cost inp B s +
        ((forLoop (g + 11) (g + 4) (g + 13) (seqs [lit (g + 13) 1, ar .sub (g + 10) (g + 10) (g + 13),
      ar .div (g + 9) (g + 9) (g + 14), ar .lt (g + 12) (g + 10) (g + 1),
      .ifz (g + 12) (seqs [ar .div (g + 15) (g + 8) (g + 9), ar .mod (g + 15) (g + 15) (g + 14),
        .ifz (g + 15) .skip (seqs [ar .div (g + 15) (g + 9) (g + 2), ar .mul (g + 15) g (g + 15),
          ar .xor (g + 8) (g + 8) (g + 15)])]) .skip])).cost inp B s1 + 0) := by
      simp only [gfRem, cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, exec_seqs_nil, hs1]; ring
    rw [hc]
    have c0 : (seqs [cp (g + 9) (g + 5), cp (g + 10) (g + 4), lit (g + 14) 2]).cost
        inp B s ≤ 3 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons,
        exec_lit, exec_cp, HS.setR_regs, upd_ne, upd_eq, hPN, ← hN]
      have := kappa_bits_le B (a := 2 ^ N) (M := M) (by omega)
      have := kappa_bits_le B (a := 2) (M := M) (by have : 1 ≤ 2 ^ N := Nat.one_le_two_pow; omega)
      have := kappa_bits_le B (a := N) (M := M) (by omega)
      omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k3
    have := kappa_bits_le B (a := N) (M := M) (by omega)
    nlinarith


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
-- module Solutions.EditMulticoloring.RamParams
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Part P (q379): logarithms and powers

Register convention: inputs in arbitrary registers below `S`; outputs at `S`, `S + 1`, …;
scratch above the outputs.  Each program's frame lemma lists the registers it may write.

* `floorLogW b N T S`: `S := Nat.log (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`
  (needs `Nat.log … ≤ regs T`, loop count `regs T`); writes `S .. S+3`.
* `ceilLogW b N T S`: `S := ceilLog (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`; `S .. S+3`.
* `powW a e S`: `S := regs a ^ regs e`; writes only `S`.
* `radW q t lR S`: `S := radiusBound q (2 t) (regs lR)`; writes `S .. S+2`.
* `rhoW q t nR hR qhR S`: `S := shortLength q t (regs hR)`; writes `S .. S+8`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Logs
variable (inp : ℕ → ℕ) (B : ℕ)

theorem powW_frame (a e S : ℕ) (s : HS) (r' : ℕ) (h : r' ≠ S) :
    ((powW a e S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [powW, Cmd.wregs, lit, ar, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem powW_spec (a e S : ℕ) (s : HS) (M : ℕ) (ha : a ≠ S) (he : e ≠ S) (h1 : 1 ≤ s.regs a)
    (hM : s.regs a ^ s.regs e + s.regs a + s.regs e ≤ M) :
    ((powW a e S).exec inp s).regs S = s.regs a ^ s.regs e ∧
    (∀ r', r' ≠ S → ((powW a e S).exec inp s).regs r' = s.regs r') ∧
    ((powW a e S).exec inp s).mem = s.mem ∧
    ((powW a e S).exec inp s).cur = s.cur ∧
    ((powW a e S).exec inp s).out = s.out ∧
    (powW a e S).cost inp B s ≤ (2 * s.regs e + 3) * kappa B (RAM.bits M) := by
  set A := s.regs a with hA
  set E := s.regs e with hE
  set s1 := s.setR S 1 with hs1
  have he1 : s1.regs e = E := by simp (disch := omega) [hs1, upd_ne, hE]
  have K := loop_spec inp B e (ar .mul S S a) s1
    (fun k st => st.regs S = A ^ k ∧ ∀ r', r' ≠ S → st.regs r' = s.regs r')
    (fun _ => kappa B (RAM.bits M))
    ⟨by simp [hs1], fun r' h => by simp (disch := omega) [hs1, upd_ne]⟩
    (by
      intro k hk st ⟨hc, hr⟩
      rw [he1] at hk
      have ea : st.regs a = A := hr a ha
      refine ⟨⟨by simp [hc, ea, pow_succ], fun r' h => by simp (disch := omega) [upd_ne, hr r' h]⟩, ?_⟩
      simp only [cost_ar, hc, ea]
      apply kappa_bits_le
      have := Nat.pow_le_pow_right h1 hk.le
      omega)
  obtain ⟨⟨k1, k2⟩, k3⟩ := K
  rw [he1] at k1 k3
  refine ⟨k1, powW_frame inp a e S s, exec_mem_of_stores inp _ rfl s,
    exec_cur_of_reads inp _ rfl s, exec_out_of_emits inp _ rfl s, ?_⟩
  have hco : (powW a e S).cost inp B s = kappa B (RAM.bits 1) + (Cmd.loop e (ar .mul S S a)).cost inp B s1 := rfl
  rw [hco]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k3
  have := kappa_bits_le B (a := E) (M := M) (by omega)
  have := kappa_bits_le B (a := 1) (M := M) (by omega)
  nlinarith

/-! ### The short length `ρ = shortLength q t h` -/

end Logs

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams3
/-!
# Part P (q379): the modulus search

`modTest b p`: no binary polynomial `d` with `2 ≤ d < 2^b` (degree `1 .. b-1`) divides `p`.
`modSearch b`: the first `p ∈ [2^b, 2^(b+1))` passing `modTest b`, else `0`.

`modulusW bR S` computes `S := modSearch (regs bR)` by two nested loops of `2^b` iterations
around `gfSetup` / `gfRem` (block `g = S + 10`).  Writes only registers `S .. S+25`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Modulus
variable (inp : ℕ → ℕ) (B : ℕ)

theorem mtBody_frame (S : ℕ) (s : HS) (r' : ℕ) (h4 : r' ≠ S + 4) (h9 : r' ≠ S + 9)
    (h : r' < S + 10 ∨ r' = S + 13 ∨ r' = S + 16 ∨ r' = S + 17 ∨ S + 26 ≤ r') :
    ((mtBody S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [mtBody, gfSetup, gfRem, forLoop, seqs, Cmd.wregs, lit, ar, cp, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem mtBody_spec (S : ℕ) (s : HS) (b M : ℕ) (hW : s.regs (S + 13) = b + 1)
    (hd : s.regs (S + 7) < 2 ^ b) (hp : s.regs (S + 3) < 2 ^ (b + 1))
    (hM : (2 ^ b + 4) * 2 ^ (2 * (b + 1)) ≤ M) :
    ((mtBody S).exec inp s).regs (S + 4) =
      (if (decide (s.regs (S + 7) < 2) || binaryRem (s.regs (S + 7)) (s.regs (S + 3)) != 0)
        then s.regs (S + 4) else 0) ∧
    ((mtBody S).exec inp s).mem = s.mem ∧
    (mtBody S).cost inp B s ≤ (44 * b + 80) * kappa B (RAM.bits M) := by
  set d := s.regs (S + 7) with hdd
  set p := s.regs (S + 3) with hpd
  set W := b + 1 with hWd
  have hX : 2 ^ (2 * W) = 2 ^ W * 2 ^ W := by rw [two_mul, pow_add]
  have hbW : 2 ^ b < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1W : 1 ≤ 2 ^ W := Nat.one_le_two_pow
  have hpX : p < 2 ^ (2 * W) := by rw [hX]; nlinarith
  have hMX : 4 * 2 ^ (2 * W) ≤ M := by nlinarith
  have hpM : p + 2 ^ (2 * W) ≤ M := by nlinarith
  have hbM : W + 2 ≤ M := by
    have : W < 2 ^ W := Nat.lt_two_pow_self
    nlinarith
  have hstore : (mtBody S).stores = false := rfl
  have e1 := kappa_bits_le B (a := 1) (M := M) (by omega)
  have hdX : d < 2 ^ (2 * W) := lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega))
  have e2 := kappa_bits_le B (a := 1 + d) (M := M) (by omega)
  have e0 := kappa_bits_le B (a := 0) (M := M) (by omega)
  set s1 := (ar .lt (S + 9) (S + 9) (S + 7)).exec inp ((lit (S + 9) 1).exec inp s) with hs1
  have f1 : ∀ r', r' ≠ S + 9 → s1.regs r' = s.regs r' := fun r' h => by
    simp (disch := omega) [hs1, upd_ne]
  have f19 : s1.regs (S + 9) = if 1 < d then 1 else 0 := by simp [hs1, hdd]
  have hcost1 : (mtBody S).cost inp B s = kappa B (RAM.bits 1) + (kappa B (RAM.bits (1 + d)) +
      ((Cmd.ifz (S + 9) .skip (seqs [cp (S + 10) (S + 7), gfSetup (S + 10), cp (S + 18) (S + 3),
      gfRem (S + 10), .ifz (S + 18) (lit (S + 4) 0) .skip])).cost inp B s1 + 0)) := by
    rw [mtBody, cost_seqs_cons, cost_seqs_cons, cost_seqs_cons, cost_seqs_nil, ← hs1]
    simp (disch := omega) [upd_ne, hdd]
  have hex1 : (mtBody S).exec inp s = (Cmd.ifz (S + 9) .skip (seqs [cp (S + 10) (S + 7),
      gfSetup (S + 10), cp (S + 18) (S + 3), gfRem (S + 10),
      .ifz (S + 18) (lit (S + 4) 0) .skip])).exec inp s1 := by
    rw [mtBody, exec_seqs_cons, exec_seqs_cons, exec_seqs_cons, exec_seqs_nil, ← hs1]
  by_cases hd1 : 1 < d
  swap
  · refine ⟨?_, exec_mem_of_stores inp _ hstore s, ?_⟩
    · -- value, `d ≤ 1`
      rw [hex1, exec_ifz, if_pos (by rw [f19, if_neg hd1])]
      rw [if_pos (by simp; omega)]
      exact f1 _ (by omega)
    · -- cost, `d ≤ 1`
      rw [hcost1, cost_ifz, if_pos (by rw [f19, if_neg hd1]), f19, if_neg hd1, cost_skip]
      have hy : (44 * b + 80) * kappa B (RAM.bits M) = 44 * b * kappa B (RAM.bits M) +
        80 * kappa B (RAM.bits M) := by ring
      omega
  have hc1 : ¬ s1.regs (S + 9) = 0 := by rw [f19, if_pos hd1]; omega
  set s2 := (cp (S + 10) (S + 7)).exec inp s1 with hs2
  have g2 : ∀ r', r' ≠ S + 10 → r' ≠ S + 9 → s2.regs r' = s.regs r' := fun r' h h' => by
    rw [hs2, exec_cp, HS.setR_regs, upd_ne h, f1 _ h']
  have g20 : s2.regs (S + 10) = d := by rw [hs2, exec_cp, HS.setR_regs, upd_eq rfl, f1 _ (by omega)]
  have hdW : d < 2 ^ W := hd.trans hbW
  have hdM : d * 2 ^ (2 * W) + 4 * 2 ^ (2 * W) ≤ M := by
    have : d * 2 ^ (2 * W) ≤ 2 ^ b * 2 ^ (2 * W) := Nat.mul_le_mul_right _ hd.le
    have h' : (2 ^ b + 4) * 2 ^ (2 * W) = 2 ^ b * 2 ^ (2 * W) + 4 * 2 ^ (2 * W) := add_mul _ _ _
    omega
  obtain ⟨c1, c2, c3, -, -, c6⟩ := gfSetup_spec inp B (S + 10) s2 d W M g20
    (by rw [g2 _ (by omega) (by omega), hW]) (by omega) hdW hdM
  set s3 := (gfSetup (S + 10)).exec inp s2 with hs3
  set s4 := (cp (S + 18) (S + 3)).exec inp s3 with hs4
  have g4 : ∀ r', r' ≠ S + 18 → s4.regs r' = s3.regs r' := fun r' h => by
    rw [hs4, exec_cp, HS.setR_regs, upd_ne h]
  have g48 : s4.regs (S + 18) = p := by
    rw [hs4, exec_cp, HS.setR_regs, upd_eq rfl, c2 _ (by omega) (by omega) (by omega) (by omega)
      (by omega), g2 _ (by omega) (by omega)]
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := c1
  have hctx4 : GFCtx s4 (S + 10) d W := GFCtx.congr ⟨q0, q1, q2, q3, q4, q5⟩
    (fun r h1 h2 => g4 r (by omega))
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hctx4
  obtain ⟨m1, m2, m3, -, -, m6⟩ := gfRem_spec inp B (S + 10) s4 M (by rw [r0]; omega)
    (by rw [r1, r0]) (by rw [r2, r0]) (by rw [r5, r4]) (by rw [g48, r4]; exact hpX)
    (by rw [r0, r4]; exact hdM)
  rw [g48, r0] at m1
  rw [r4] at m6
  set s5 := (gfRem (S + 10)).exec inp s4 with hs5
  have g54 : s5.regs (S + 4) = s.regs (S + 4) := by
    rw [m2 _ (by omega), g4 _ (by omega), c2 _ (by omega) (by omega) (by omega) (by omega)
      (by omega), g2 _ (by omega) (by omega)]
  have hex2 : (mtBody S).exec inp s = (Cmd.ifz (S + 18) (lit (S + 4) 0) .skip).exec inp s5 := by
    rw [hex1, exec_ifz, if_neg hc1, exec_seqs_cons, ← hs2, exec_seqs_cons, ← hs3, exec_seqs_cons,
      ← hs4, exec_seqs_cons, ← hs5, exec_seqs_cons, exec_seqs_nil]
  have hrlt : binaryRem d p ≤ d := by
    have := binaryRem_lt d p (by omega)
    have := two_pow_log2_le d (by omega)
    omega
  refine ⟨?_, exec_mem_of_stores inp _ hstore s, ?_⟩
  · rw [hex2, exec_ifz, m1]
    by_cases h0 : binaryRem d p = 0
    · rw [if_pos h0, if_neg (by simp [h0]; omega)]; simp
    · rw [if_neg h0, if_pos (by simp [h0])]; exact g54
  · rw [hcost1, cost_ifz, if_neg hc1, cost_seqs_cons, ← hs2, cost_seqs_cons, ← hs3, cost_seqs_cons,
      ← hs4, cost_seqs_cons, ← hs5, cost_seqs_cons, cost_seqs_nil, cost_ifz, m1, f19, if_pos hd1]
    have v1 : s1.regs (S + 7) = d := f1 _ (by omega)
    have v3 : s3.regs (S + 3) = p := by
      rw [c2 _ (by omega) (by omega) (by omega) (by omega) (by omega), g2 _ (by omega) (by omega)]
    simp only [cost_cp, cost_lit, cost_skip, v1, v3, ← hdd, ← hpd]
    have k1 := kappa_bits_le B (a := d) (M := M) (by omega)
    have k2 := kappa_bits_le B (a := p) (M := M) (by omega)
    have k3 := kappa_bits_le B (a := binaryRem d p) (M := M) (by omega)
    have k4 : (if binaryRem d p = 0 then kappa B (RAM.bits 0) else 0) ≤ kappa B (RAM.bits M) := by
      split_ifs <;> omega
    have hy : (44 * b + 80) * kappa B (RAM.bits M) = (16 * W + 12) * kappa B (RAM.bits M) +
      (14 * (2 * W) + 6) * kappa B (RAM.bits M) + 18 * kappa B (RAM.bits M) := by rw [hWd]; ring
    omega

theorem mtInner_frame (S : ℕ) (s : HS) (r' : ℕ)
    (h : r' < S + 4 ∨ r' = S + 5 ∨ r' = S + 6 ∨ r' = S + 13 ∨ r' = S + 16 ∨ r' = S + 17 ∨ S + 26 ≤ r') :
    ((mtInner S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [mtInner, mtBody, gfSetup, gfRem, forLoop, seqs, Cmd.wregs, lit, ar, cp,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    and_true, true_and]
  omega

theorem mtInner_spec (S : ℕ) (s : HS) (b M : ℕ) (h2 : s.regs (S + 2) = 2 ^ b)
    (hW : s.regs (S + 13) = b + 1) (hp : s.regs (S + 3) < 2 ^ (b + 1))
    (hM : (2 ^ b + 4) * 2 ^ (2 * (b + 1)) ≤ M) :
    ((mtInner S).exec inp s).regs (S + 4) = (if modTest b (s.regs (S + 3)) then 1 else 0) ∧
    ((mtInner S).exec inp s).mem = s.mem ∧
    (mtInner S).cost inp B s ≤
      (3 * (2 ^ b + 1) + 2 ^ b * (44 * b + 80) + 1) * kappa B (RAM.bits M) := by
  set p := s.regs (S + 3) with hpd
  set P := 2 ^ b with hP
  set F : ℕ → Bool := fun d => decide (d < 2) || binaryRem d p != 0 with hF
  set s1 := s.setR (S + 4) 1 with hs1
  have hn1 : s1.regs (S + 2) = P := by simp (disch := omega) [hs1, upd_ne, h2]
  have hPM : P + 1 ≤ M := by
    have : 1 ≤ 2 ^ (2 * (b + 1)) := Nat.one_le_two_pow
    nlinarith
  have K := forLoop_spec inp B (S + 7) (S + 2) (S + 8) (mtBody S) s1 (by omega) (by omega)
    (fun k st => st.regs (S + 4) = (if (List.range k).all F then 1 else 0) ∧
      st.regs (S + 3) = p ∧ st.regs (S + 13) = b + 1 ∧ st.mem = s.mem)
    (fun _ => (44 * b + 80) * kappa B (RAM.bits M))
    ⟨by simp [hs1], by simp (disch := omega) [hs1, upd_ne, hpd],
      by simp (disch := omega) [hs1, upd_ne, hW], by simp [hs1]⟩
    (by
      intro k hk st ⟨hf, hp', hw, hm⟩ hi
      rw [hn1] at hk
      obtain ⟨b1, b2, b3⟩ := mtBody_spec inp B S st b M hw (by rw [hi]; exact hk) (by rw [hp']; exact hp) hM
      rw [hi, hp', hf] at b1
      refine ⟨mtBody_frame inp S st _ (by omega) (by omega) (by omega) |>.trans hi, ⟨?_, ?_, ?_, ?_⟩, b3⟩
      · simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [b1, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
        generalize (List.range k).all F = A
        generalize hc : (decide (k < 2) || binaryRem k p != 0) = c
        have hFk : F k = c := hc
        rw [hFk]
        cases A <;> cases c <;> rfl
      · simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [mtBody_frame inp S st _ (by omega) (by omega) (by omega), hp']
      · simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [mtBody_frame inp S st _ (by omega) (by omega) (by omega), hw]
      · simp only [HS.setR_mem, b2, hm])
  obtain ⟨⟨k1, -, -, k4⟩, kc⟩ := K
  simp only [hn1] at k1 kc
  refine ⟨?_, ?_, ?_⟩
  · show ((forLoop (S + 7) (S + 2) (S + 8) (mtBody S)).exec inp s1).regs (S + 4) = _
    rw [k1]; rfl
  · exact k4
  · show kappa B (RAM.bits 1) + (forLoop (S + 7) (S + 2) (S + 8) (mtBody S)).cost inp B s1 ≤ _
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at kc
    have e1 := kappa_bits_le B (a := 1) (M := M) (by omega)
    have e2 := kappa_bits_le B (a := P) (M := M) (by omega)
    have hz : 3 * (P + 1) * kappa B (RAM.bits P) ≤ 3 * (P + 1) * kappa B (RAM.bits M) :=
      Nat.mul_le_mul_left _ e2
    have hy : (3 * (P + 1) + P * (44 * b + 80) + 1) * kappa B (RAM.bits M) =
      3 * (P + 1) * kappa B (RAM.bits M) + P * ((44 * b + 80) * kappa B (RAM.bits M)) +
        kappa B (RAM.bits M) := by ring
    omega

theorem modulusW_frame (bR S : ℕ) (s : HS) (r' : ℕ) (h : r' < S ∨ S + 26 ≤ r') :
    ((modulusW bR S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [modulusW, moBody, mtInner, mtBody, powW, gfSetup, gfRem, forLoop, seqs, Cmd.wregs,
    lit, ar, cp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or,
    not_false_eq_true, and_true, true_and]
  omega

theorem modFind_succ (b i : ℕ) : modFind b (i + 1) =
    (modFind b i).or (if modTest b (i + 2 ^ b) then some (i + 2 ^ b) else none) := by
  unfold modFind
  rw [List.range_succ, List.map_append, List.find?_append]
  congr 1
  simp only [List.map_cons, List.map_nil, List.find?_cons, List.find?_nil]
  cases modTest b (i + 2 ^ b) <;> rfl

theorem modulusW_spec_oai (bR S : ℕ) (s : HS) (M : ℕ) (hb : bR < S)
    (hM : (2 ^ s.regs bR + 4) * 2 ^ (2 * (s.regs bR + 1)) ≤ M) :
    ((modulusW bR S).exec inp s).regs S = modSearch (s.regs bR) ∧
    (∀ r', (r' < S ∨ S + 26 ≤ r') → ((modulusW bR S).exec inp s).regs r' = s.regs r') ∧
    ((modulusW bR S).exec inp s).mem = s.mem ∧
    ((modulusW bR S).exec inp s).cur = s.cur ∧
    ((modulusW bR S).exec inp s).out = s.out ∧
    (modulusW bR S).cost inp B s ≤
      (2 ^ s.regs bR + 1) ^ 2 * (44 * s.regs bR + 90) * kappa B (RAM.bits M) := by
  set b := s.regs bR with hbd
  set P := 2 ^ b with hP
  have hX1 : 1 ≤ 2 ^ (2 * (b + 1)) := Nat.one_le_two_pow
  have hPX : P ≤ 2 ^ (2 * (b + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX4 : 4 ≤ 2 ^ (2 * (b + 1)) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (b + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4P : 4 * P + 16 ≤ M := by nlinarith
  have hPM : P + 4 ≤ M := by omega
  have hbP : b < P := Nat.lt_two_pow_self
  have hP2 : 2 * P = 2 ^ (b + 1) := by rw [pow_succ]; ring
  have h2P : 2 * P ≤ M := by
    have : 2 * P ≤ 2 ^ (2 * (b + 1)) := by rw [hP2]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  set s0 := (seqs [lit S 0, lit (S + 1) 0, lit (S + 9) 2]).exec inp s with hs0
  have g0 : ∀ r', r' ≠ S → r' ≠ S + 1 → r' ≠ S + 9 → s0.regs r' = s.regs r' := fun r' a1 a2 a3 => by
    simp (disch := omega) [hs0, upd_ne]
  obtain ⟨w1, w2, -, -, -, w6⟩ := powW_spec inp B (S + 9) bR (S + 2) s0 M (by omega) (by omega)
    (by simp (disch := omega) [hs0, upd_ne, upd_eq])
    (by rw [g0 bR (by omega) (by omega) (by omega)]; simp (disch := omega) [hs0, upd_ne, upd_eq]
        simp only [← hbd, ← hP]; omega)
  set s0' := (powW (S + 9) bR (S + 2)).exec inp s0 with hs0'
  have w9 : s0.regs (S + 9) = 2 := by simp (disch := omega) [hs0, upd_ne, upd_eq]
  rw [w9] at w1
  rw [g0 bR (by omega) (by omega) (by omega)] at w1 w6
  set s1 := (ar .add (S + 13) bR (S + 9)).exec inp ((lit (S + 9) 1).exec inp s0') with hs1
  have hpre : (seqs [lit S 0, lit (S + 1) 0, lit (S + 9) 2, powW (S + 9) bR (S + 2), lit (S + 9) 1,
      ar .add (S + 13) bR (S + 9)]).exec inp s = s1 := rfl
  have hprec : (seqs [lit S 0, lit (S + 1) 0, lit (S + 9) 2, powW (S + 9) bR (S + 2), lit (S + 9) 1,
      ar .add (S + 13) bR (S + 9)]).cost inp B s ≤ (2 * b + 8) * kappa B (RAM.bits M) := by
    have hs0eq : ((s.setR S 0).setR (S + 1) 0).setR (S + 9) 2 = s0 := rfl
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_seqs_cons, exec_lit, exec_ar,
      HS.setR_regs]
    rw [hs0eq, ← hs0']
    simp (disch := omega) only [upd_ne, upd_eq, w2 bR (by omega), g0 bR (by omega) (by omega) (by omega)]
    rw [← hbd]
    have := kappa_bits_le B (a := 0) (M := M) (by omega)
    have := kappa_bits_le B (a := 2) (M := M) (by omega)
    have := kappa_bits_le B (a := 1) (M := M) (by omega)
    have := kappa_bits_le B (a := b + 1) (M := M) (by omega)
    rw [← hbd] at w6
    have hy : (2 * b + 8) * kappa B (RAM.bits M) = (2 * b + 3) * kappa B (RAM.bits M) +
      5 * kappa B (RAM.bits M) := by ring
    omega
  have v0 : ∀ r', r' ≠ S → r' ≠ S + 1 → r' ≠ S + 2 → r' ≠ S + 9 → r' ≠ S + 13 →
      s1.regs r' = s.regs r' := fun r' a1 a2 a3 a4 a5 => by
    rw [hs1]; simp (disch := omega) only [exec_ar, exec_lit, HS.setR_regs, upd_ne]
    rw [w2 _ a3, g0 _ a1 a2 a4]
  have vS : s1.regs S = 0 := by
    rw [hs1]; simp (disch := omega) only [exec_ar, exec_lit, HS.setR_regs, upd_ne]
    rw [w2 _ (by omega), hs0]; simp (disch := omega) [upd_ne]
  have vS1 : s1.regs (S + 1) = 0 := by
    rw [hs1]; simp (disch := omega) only [exec_ar, exec_lit, HS.setR_regs, upd_ne]
    rw [w2 _ (by omega), hs0]; simp (disch := omega) [upd_ne]
  have vS2 : s1.regs (S + 2) = P := by
    rw [hs1]; simp (disch := omega) only [exec_ar, exec_lit, HS.setR_regs, upd_ne]
    rw [w1]
  have vS13 : s1.regs (S + 13) = b + 1 := by
    rw [hs1]; simp (disch := omega) only [exec_ar, exec_lit, HS.setR_regs, upd_ne, upd_eq, arith_add]
    rw [w2 _ (by omega), g0 _ (by omega) (by omega) (by omega)]
  have vm : s1.mem = s.mem := by
    have := exec_mem_of_stores inp (seqs [lit S 0, lit (S + 1) 0, lit (S + 9) 2,
      powW (S + 9) bR (S + 2), lit (S + 9) 1, ar .add (S + 13) bR (S + 9)]) rfl s
    rw [hpre] at this; exact this
  set C := (3 * (P + 1) + P * (44 * b + 80) + 6) * kappa B (RAM.bits M) with hC
  have hinit : ∀ r', (r' < S ∨ S + 26 ≤ r') → (s1.setR (S + 5) 0).regs r' = s.regs r' := by
    intro r' h
    simp (disch := omega) only [HS.setR_regs, upd_ne]
    exact v0 r' (by omega) (by omega) (by omega) (by omega) (by omega)
  have K := forLoop_spec inp B (S + 5) (S + 2) (S + 6) (moBody S) s1 (by omega) (by omega)
    (fun i st => st.regs (S + 1) = (if (modFind b i).isSome then 1 else 0) ∧
      st.regs S = (modFind b i).getD 0 ∧ st.regs (S + 2) = P ∧ st.regs (S + 13) = b + 1 ∧
      (∀ r', (r' < S ∨ S + 26 ≤ r') → st.regs r' = s.regs r') ∧ st.mem = s.mem)
    (fun _ => C)
    ⟨by simp (disch := omega) [upd_ne, vS1, modFind], by simp (disch := omega) [upd_ne, vS, modFind],
      by simp (disch := omega) [upd_ne, vS2], by simp (disch := omega) [upd_ne, vS13],
      hinit, by simp [vm]⟩
    (by
      intro i hi st ⟨hf, hres, h2, h13, hr, hm⟩ hidx
      rw [vS2] at hi
      set sa := (ar .add (S + 3) (S + 5) (S + 2)).exec inp st with hsa
      have a3 : sa.regs (S + 3) = i + P := by simp [hsa, hidx, h2]
      have ar' : ∀ r', r' ≠ S + 3 → sa.regs r' = st.regs r' := fun r' h => by
        simp (disch := omega) [hsa, upd_ne]
      have hiP : i + P < 2 ^ (b + 1) := by omega
      obtain ⟨n1, n2, n3⟩ := mtInner_spec inp B S sa b M (by rw [ar' _ (by omega), h2])
        (by rw [ar' _ (by omega), h13]) (by rw [a3]; exact hiP) (by rw [← hP]; exact hM)
      rw [a3] at n1
      set sb := (mtInner S).exec inp sa with hsb
      have bfr : ∀ r', (r' < S + 3 ∨ r' = S + 5 ∨ r' = S + 6 ∨ r' = S + 13 ∨ S + 26 ≤ r') →
          sb.regs r' = st.regs r' := fun r' h => by
        rw [hsb, mtInner_frame inp S sa r' (by omega), ar' _ (by omega)]
      have b3 : sb.regs (S + 3) = i + P := by rw [hsb, mtInner_frame inp S sa _ (by omega), a3]
      have hex : (moBody S).exec inp st = (Cmd.ifz (S + 1) (.ifz (S + 4) .skip
          (seqs [cp S (S + 3), lit (S + 1) 1])) .skip).exec inp sb := rfl
      have hco : (moBody S).cost inp B st = kappa B (RAM.bits (i + P)) + ((mtInner S).cost inp B sa +
          ((Cmd.ifz (S + 1) (.ifz (S + 4) .skip
          (seqs [cp S (S + 3), lit (S + 1) 1])) .skip).cost inp B sb + 0)) := by
        show kappa B (RAM.bits (st.regs (S + 5) + st.regs (S + 2))) + _ = _
        rw [hidx, h2]; rfl
      have hsucc := modFind_succ b i
      rw [← hP] at hsucc
      have e1 := kappa_bits_le B (a := i + P) (M := M) (by omega)
      have e2 := kappa_bits_le B (a := 1) (M := M) (by omega)
      have e0 := kappa_bits_le B (a := 0) (M := M) (by omega)
      have hmt : (mtInner S).cost inp B sa ≤ (3 * (P + 1) + P * (44 * b + 80) + 1) * kappa B (RAM.bits M) := n3
      have hCe : C = (3 * (P + 1) + P * (44 * b + 80) + 1) * kappa B (RAM.bits M) +
        5 * kappa B (RAM.bits M) := by rw [hC]; ring
      have sb1 : sb.regs (S + 1) = st.regs (S + 1) := bfr _ (by omega)
      have sb0 : sb.regs S = st.regs S := bfr _ (by omega)
      have hframe : ∀ st' : HS, (∀ r', r' ≠ S → r' ≠ S + 1 → st'.regs r' = sb.regs r') →
          (∀ r', (r' < S ∨ S + 26 ≤ r') → ((st'.setR (S + 6) 1).setR (S + 5) (i + 1)).regs r' = s.regs r') ∧
          ((st'.setR (S + 6) 1).setR (S + 5) (i + 1)).regs (S + 2) = P ∧
          ((st'.setR (S + 6) 1).setR (S + 5) (i + 1)).regs (S + 13) = b + 1 := by
        intro st' hst'
        refine ⟨fun r' h => ?_, ?_, ?_⟩
        · simp (disch := omega) only [HS.setR_regs, upd_ne]
          rw [hst' _ (by omega) (by omega), bfr _ (by omega)]; exact hr r' h
        · simp (disch := omega) only [HS.setR_regs, upd_ne]
          rw [hst' _ (by omega) (by omega), bfr _ (by omega)]; exact h2
        · simp (disch := omega) only [HS.setR_regs, upd_ne]
          rw [hst' _ (by omega) (by omega), bfr _ (by omega)]; exact h13
      have hmem : sb.mem = s.mem := by rw [hsb, n2, hsa]; simpa using hm
      rcases hmf : modFind b i with _ | x
      · -- not found yet
        rw [hmf] at hf hres hsucc
        simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hf
        simp only [Option.none_or] at hsucc
        by_cases ht : modTest b (i + P)
        · rw [if_pos ht] at n1 hsucc
          set sc := (sb.setR S (i + P)).setR (S + 1) 1 with hsc
          have hex' : (moBody S).exec inp st = sc := by
            rw [hex]; simp (disch := omega) [sb1, hf, n1, b3, hsc]
          rw [hex']
          obtain ⟨z1, z2, z3⟩ := hframe sc (fun r' a1 a2 => by simp (disch := omega) [hsc, upd_ne])
          refine ⟨by simp (disch := omega) [hsc, upd_ne, sb0, hres, hidx, bfr], ⟨?_, ?_, z2, z3, z1, ?_⟩, ?_⟩
          · simp (disch := omega) [hsc, upd_ne, upd_eq, hsucc]
          · simp (disch := omega) [hsc, upd_ne, upd_eq, hsucc]
          · simp [hsc, hmem]
          · rw [hco]
            simp (disch := omega) only [cost_ifz, sb1, hf, if_true, n1, one_ne_zero, if_false,
              cost_seqs_cons, cost_seqs_nil, cost_cp, cost_lit, b3, bits_one]
            simp only [bits_zero, bits_one] at e0 e2 ⊢
            omega
        · rw [if_neg ht] at n1 hsucc
          have hex' : (moBody S).exec inp st = sb := by
            rw [hex]; simp (disch := omega) [sb1, hf, n1]
          rw [hex']
          obtain ⟨z1, z2, z3⟩ := hframe sb (fun r' _ _ => rfl)
          refine ⟨by rw [bfr _ (by omega)]; exact hidx, ⟨?_, ?_, z2, z3, z1, ?_⟩, ?_⟩
          · simp (disch := omega) [upd_ne, sb1, hf, hsucc]
          · simp (disch := omega) [upd_ne, sb0, hres, hsucc]
          · simp [hmem]
          · rw [hco]
            simp (disch := omega) only [cost_ifz, sb1, hf, if_true, n1, cost_skip]
            simp only [bits_zero, bits_one] at e0 e2 ⊢
            omega
      · -- already found
        rw [hmf] at hf hres hsucc
        simp only [Option.isSome_some, if_true] at hf
        simp only [Option.some_or] at hsucc
        have hex' : (moBody S).exec inp st = sb := by
          rw [hex]; simp [sb1, hf]
        rw [hex']
        obtain ⟨z1, z2, z3⟩ := hframe sb (fun r' _ _ => rfl)
        refine ⟨by rw [bfr _ (by omega)]; exact hidx, ⟨?_, ?_, z2, z3, z1, ?_⟩, ?_⟩
        · simp (disch := omega) [upd_ne, sb1, hf, hsucc]
        · simp (disch := omega) [upd_ne, sb0, hres, hsucc]
        · simp [hmem]
        · rw [hco]
          simp (disch := omega) only [cost_ifz, sb1, hf, one_ne_zero, if_false, cost_skip, bits_one]
          simp only [bits_zero, bits_one] at e0 e2 ⊢
          omega)
  obtain ⟨⟨k1, k2, -, -, k5, k6⟩, k7⟩ := K
  simp only [vS2] at k1 k2 k7
  have hex : (modulusW bR S).exec inp s = (forLoop (S + 5) (S + 2) (S + 6) (moBody S)).exec inp s1 := by
    rw [modulusW, exec_seq, hpre]
  refine ⟨?_, modulusW_frame inp bR S s, by rw [hex]; exact k6, exec_cur_of_reads inp _ rfl s,
    exec_out_of_emits inp _ rfl s, ?_⟩
  · rw [hex, k2]; rfl
  · rw [modulusW, cost_seq, hpre]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k7
    have e1 := kappa_bits_le B (a := 1) (M := M) (by omega)
    have e2 := kappa_bits_le B (a := b + 1) (M := M) (by omega)
    have e3 := kappa_bits_le B (a := P) (M := M) (by omega)
    have hz : 3 * (P + 1) * kappa B (RAM.bits P) ≤ 3 * (P + 1) * kappa B (RAM.bits M) :=
      Nat.mul_le_mul_left _ e3
    have hpoly : (2 * b + 8) + 3 * (P + 1) + P * (3 * (P + 1) + P * (44 * b + 80) + 6) ≤
        (P + 1) ^ 2 * (44 * b + 90) := by nlinarith
    have hy := Nat.mul_le_mul_right (kappa B (RAM.bits M)) hpoly
    have hy2 : ((2 * b + 8) + 3 * (P + 1) + P * (3 * (P + 1) + P * (44 * b + 80) + 6)) *
        kappa B (RAM.bits M) = (2 * b + 8) * kappa B (RAM.bits M) +
        3 * (P + 1) * kappa B (RAM.bits M) + P * C := by rw [hC]; ring
    omega

end Modulus

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.modulusW_spec_oai := @EditMulticoloring.Dev.Ram.modulusW_spec_oai
