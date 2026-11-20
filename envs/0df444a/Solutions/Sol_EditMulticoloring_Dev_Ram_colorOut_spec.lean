-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.colorOut_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:55.899239+00:00
-- url     : https://prove2.me/submissions/02d0301f-0485-4ba1-994c-7281c18e9b36

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

theorem binaryMul_fold (a b N : ℕ) (hb : b < 2 ^ N) :
    binaryMul a b = (List.range N).foldl (mulStep b a) 0 := by
  have hn := lt_two_pow_min hb
  have hst : ∀ i, min N (b.log2 + 1) ≤ i → ∀ y, mulStep b a y i = y := by
    intro i hi y; simp [mulStep, testBit_false_of_lt_pow hn hi]
  have e1 := foldl_range_stable (mulStep b a) 0 _ hst N (min_le_left _ _)
  have e2 := foldl_range_stable (mulStep b a) 0 _ hst (b.log2 + 1) (min_le_right _ _)
  rw [e1, ← e2]; rfl

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

theorem gfField_spec (g : ℕ) (s : HS) (p W M : ℕ) (hctx : GFCtx s g p W) (hp : p ≠ 0)
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

theorem bitEval_fold (Q p K id a : ℕ) :
    bitEval Q p K id a = (List.range K).foldl
      (fun z k => Nat.xor (fieldMul p z a) ((id / Q ^ (K - 1 - k)) % Q)) 0 := by
  unfold bitEval
  rw [range_reverse_eq_map, List.foldl_map]

theorem bitEvalW_spec (g : ℕ) (s : HS) (p W Q id M : ℕ) (hctx : GFCtx s g p W) (hp : p ≠ 0)
    (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W) (ha : s.regs (g + 7) < 2 ^ W)
    (hD : ∀ i < s.regs (g + 18), s.arr (s.regs (g + 16)) (s.regs (g + 17) + i) = (id / Q ^ i) % Q)
    (hM : p * 2 ^ (2 * W) + 4 * 2 ^ (2 * W) + s.regs (g + 16) + s.regs (g + 17) + 2 * s.regs (g + 18) ≤ M) :
    ((bitEvalW g).exec inp s).regs (g + 19) = bitEval Q p (s.regs (g + 18)) id (s.regs (g + 7)) ∧
    (∀ r', BevKeep g r' → ((bitEvalW g).exec inp s).regs r' = s.regs r') ∧
    ((bitEvalW g).exec inp s).mem = s.mem ∧
    ((bitEvalW g).exec inp s).cur = s.cur ∧
    ((bitEvalW g).exec inp s).out = s.out ∧
    (bitEvalW g).cost inp B s ≤ (s.regs (g + 18) * (36 * W + 24) + 4) * kappa B (RAM.bits M) := by
  set K := s.regs (g + 18) with hK
  set a := s.regs (g + 7) with had
  set vD := s.regs (g + 16) with hvD
  set off := s.regs (g + 17) with hoff
  set F := fun z k => Nat.xor (fieldMul p z a) ((id / Q ^ (K - 1 - k)) % Q) with hF
  have hWW : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hFlt : ∀ k, (List.range k).foldl F 0 < 2 ^ W := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, hF]
      apply Nat.xor_lt_two_pow
      · exact lt_of_lt_of_le (fieldMul_lt p _ _ hp)
          (le_trans (two_pow_log2_le p hp) hpW.le)
      · exact lt_of_lt_of_le (Nat.mod_lt _ hQ0) hQW
  set s1 := (lit (g + 19) 0).exec inp s with hs1
  have hn1 : s1.regs (g + 18) = K := by simp (disch := omega) [hs1, upd_ne, hK]
  have KL := forLoop_spec inp B (g + 20) (g + 18) (g + 22) (bevBody g) s1 (by omega) (by omega)
    (fun k st => st.regs (g + 19) = (List.range k).foldl F 0 ∧
      (∀ r', BevKeep g r' → st.regs r' = s.regs r') ∧ st.mem = s.mem)
    (fun _ => (36 * W + 21) * kappa B (RAM.bits M))
    ⟨by simp [hs1], fun r' h => by
      unfold BevKeep at h; simp (disch := omega) [hs1, upd_ne], by simp [hs1]⟩
    (by
      intro k hk st ⟨hz, hr, hm⟩ hj
      rw [hn1] at hk
      set z := (List.range k).foldl F 0 with hzd
      have hctx' : GFCtx (st.setR (g + 6) z) g p W :=
        hctx.congr (fun r h1 h2 => by
          simp (disch := omega) only [HS.setR_regs, upd_ne]; exact hr r (by unfold BevKeep; omega))
      have ha' : (st.setR (g + 6) z).regs (g + 7) = a := by
        simp (disch := omega) only [HS.setR_regs, upd_ne]; exact hr _ (by unfold BevKeep; omega)
      obtain ⟨f1, f2, f3, -, -, f6⟩ := gfField_spec inp B g (st.setR (g + 6) z) p W M hctx' hp
        (by simp; exact hFlt k) (by rw [ha']; exact ha) (by omega)
      set s2 := (gfField g).exec inp (st.setR (g + 6) z) with hs2
      simp only [HS.setR_regs, Function.update_self, ha'] at f1
      have e16 : s2.regs (g + 16) = vD := by
        rw [f2 _ (by omega)]; simp (disch := omega) only [HS.setR_regs, upd_ne]
        exact hr _ (by unfold BevKeep; omega)
      have e17 : s2.regs (g + 17) = off := by
        rw [f2 _ (by omega)]; simp (disch := omega) only [HS.setR_regs, upd_ne]
        exact hr _ (by unfold BevKeep; omega)
      have e18 : s2.regs (g + 18) = K := by
        rw [f2 _ (by omega)]; simp (disch := omega) only [HS.setR_regs, upd_ne]
        exact hr _ (by unfold BevKeep; omega)
      have e20 : s2.regs (g + 20) = k := by
        rw [f2 _ (by omega)]; simp (disch := omega) only [HS.setR_regs, upd_ne]; exact hj
      have m2 : s2.mem = s.mem := by rw [f3]; exact hm
      have hdig : s2.arr vD (off + K - 1 - k) = (id / Q ^ (K - 1 - k)) % Q := by
        have := hD (K - 1 - k) (by omega)
        rw [← this]; simp only [HS.arr, m2]; congr 2; omega
      have hex : (bevBody g).exec inp st = (seqs (bevRest g)).exec inp s2 := by
        simp only [bevBody, exec_seqs_cons, exec_cp, hz, hs2]
      have hcost : (bevBody g).cost inp B st = kappa B (RAM.bits z) +
          ((gfField g).cost inp B (st.setR (g + 6) z) + (seqs (bevRest g)).cost inp B s2) := by
        simp only [bevBody, cost_seqs_cons, exec_seqs_cons, cost_cp, exec_cp, hz, hs2]
      have hdl : (id / Q ^ (K - 1 - k)) % Q < 2 ^ W := lt_of_lt_of_le (Nat.mod_lt _ hQ0) hQW
      have hfl : fieldMul p z a < 2 ^ W :=
        lt_of_lt_of_le (fieldMul_lt p _ _ hp) (le_trans (two_pow_log2_le p hp) hpW.le)
      rw [hex, hcost]
      simp (disch := omega) only [bevRest, exec_seqs_cons, exec_seqs_nil, exec_ar, exec_lit, exec_ald,
        arith_add, arith_sub, arith_xor, HS.setR_regs, HS.setR_arr, upd_ne, upd_eq, e16, e17, e18, e20,
        f1, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_lit, cost_ald]
      rw [hdig]
      refine ⟨trivial, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [List.range_succ, List.foldl_append]; rfl
      · intro r' h
        unfold BevKeep at h
        simp (disch := omega) only [upd_ne, HS.setR_regs]
        rw [f2 _ (by omega)]; simp (disch := omega) only [HS.setR_regs, upd_ne]; exact hr r' h
      · simpa using m2
      · have := hFlt k
        have K1 := kappa_bits_le B (a := z) (M := M) (by omega)
        have K2 := kappa_bits_le B (a := off + K) (M := M) (by omega)
        have K3 := kappa_bits_le B (a := 1) (M := M) (by omega)
        have K4 := kappa_bits_le B (a := off + K + 1) (M := M) (by omega)
        have K5 := kappa_bits_le B (a := off + K - 1 + k) (M := M) (by omega)
        have K6 := kappa_bits_le B (a := vD + (off + K - 1 - k) + id / Q ^ (K - 1 - k) % Q) (M := M)
          (by omega)
        have K7 := kappa_bits_le B (a := fieldMul p z a + id / Q ^ (K - 1 - k) % Q) (M := M)
          (by omega)
        have : (36 * W + 21) * kappa B (RAM.bits M) =
          (36 * W + 14) * kappa B (RAM.bits M) + 7 * kappa B (RAM.bits M) := by ring
        omega)
  rw [hn1] at KL
  obtain ⟨⟨k1, k2, -⟩, k3⟩ := KL
  have hex : (bitEvalW g).exec inp s = (forLoop (g + 20) (g + 18) (g + 22) (bevBody g)).exec inp s1 :=
    rfl
  have hcur : ((bitEvalW g).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((bitEvalW g).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  have hmem : ((bitEvalW g).exec inp s).mem = s.mem := exec_mem_of_stores inp _ rfl s
  refine ⟨?_, ?_, hmem, hcur, hout, ?_⟩
  · rw [hex, k1, bitEval_fold]
  · rw [hex]; exact k2
  · have hc : (bitEvalW g).cost inp B s = kappa B (RAM.bits 0) +
        (forLoop (g + 20) (g + 18) (g + 22) (bevBody g)).cost inp B s1 := rfl
    rw [hc]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k3
    have := kappa_bits_le B (a := K) (M := M) (by omega)
    have := kappa_bits_le B (a := 0) (M := M) (by omega)
    nlinarith

end Prog

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

section Out
variable (inp : ℕ → ℕ) (B : ℕ)

theorem colorOut_spec_oai (g : ℕ) (s : HS) (p W Q K DG α id Ms : ℕ)
    (hctx : GFCtx s g p W) (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (h16 : s.regs (g + 16) = DG) (h18 : s.regs (g + 18) = K) (h24 : s.regs (g + 24) = Q)
    (h27 : s.regs (g + 27) = α) (hα : α < Q)
    (hrow : ∀ i < K, s.arr DG i = (id / Q ^ i) % Q)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + 2 * K ≤ Ms) :
    ((colorOut g).exec inp s).regs (g + 36) = Q * α + bitEval Q p K id α ∧
    (∀ r, KeepS g r → ((colorOut g).exec inp s).regs r = s.regs r) ∧
    ((colorOut g).exec inp s).mem = s.mem ∧
    ((colorOut g).exec inp s).cur = s.cur ∧ ((colorOut g).exec inp s).out = s.out ∧
    (colorOut g).cost inp B s ≤ (K * (36 * W + 24) + 8) * kappa B (RAM.bits Ms) := by
  have hWW : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQQ : Q * Q ≤ 2 ^ (2 * W) := by
    calc Q * Q ≤ 2 ^ W * 2 ^ W := Nat.mul_le_mul hQW hQW
      _ = 2 ^ (2 * W) := by rw [← pow_add]; congr 1; omega
  set P1 := seqs [cp (g + 7) (g + 27), lit (g + 17) 0] with hP1
  set t1 := P1.exec inp s with ht1
  have r1 : ∀ r, (r ≠ g + 7 ∧ r ≠ g + 17) → t1.regs r = s.regs r := by
    intro r hr; simp (disch := omega) [ht1, hP1, upd_ne]
  have m1 : t1.mem = s.mem := by simp [ht1, hP1]
  have v7 : t1.regs (g + 7) = α := by simp (disch := omega) [ht1, hP1, upd_ne, h27]
  have v17 : t1.regs (g + 17) = 0 := by simp (disch := omega) [ht1, hP1, upd_ne]
  have c1 : P1.cost inp B s ≤ 2 * kappa B (RAM.bits Ms) := by
    simp (disch := omega) only [hP1, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_cp, HS.setR_regs, upd_ne, upd_eq, h27]
    have := kappa_bits_le B (a := α) (M := Ms) (by omega)
    have := kappa_bits_le B (a := 0) (M := Ms) (by omega)
    omega
  have hctx1 : GFCtx t1 g p W := hctx.congr (fun r h1 h2 => r1 r (by omega))
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := bitEvalW_spec inp B g t1 p W Q id Ms hctx1 hp hpW hQ0 hQW
    (by rw [v7]; omega)
    (fun i hi => by
      rw [r1 _ (by omega), h16, v17]; rw [r1 _ (by omega), h18] at hi
      rw [show t1.arr DG (0 + i) = s.arr DG i by simp [HS.arr, m1]]; exact hrow i hi)
    (by rw [r1 _ (by omega), h16, v17, r1 _ (by omega), h18]; omega)
  rw [r1 _ (by omega), h18, v7] at b1
  rw [r1 _ (by omega), h18] at b6
  set t2 := (bitEvalW g).exec inp t1 with ht2
  have E := bitEval_lt Q p K W id α hp hpW hQ0 hQW
  have w24 : t2.regs (g + 24) = Q := by
    rw [b2 _ (by unfold BevKeep; omega), r1 _ (by omega), h24]
  have w27 : t2.regs (g + 27) = α := by
    rw [b2 _ (by unfold BevKeep; omega), r1 _ (by omega), h27]
  have hex : (colorOut g).exec inp s = (seqs [ar .mul (g + 36) (g + 24) (g + 27),
      ar .add (g + 36) (g + 36) (g + 19)]).exec inp t2 := rfl
  have hQa : Q * α ≤ Q * Q := Nat.mul_le_mul_left _ hα.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hex]; simp (disch := omega) [upd_ne, w24, w27, b1]
  · intro r h
    rw [hex]; unfold KeepS at h
    simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, HS.setR_regs, upd_ne]
    rw [b2 _ (by unfold BevKeep; omega), r1 _ (by omega)]
  · rw [hex]; simp [b3, m1]
  · rw [hex]; simp [b4, ht1, hP1]
  · rw [hex]; simp [b5, ht1, hP1]
  · have hc : (colorOut g).cost inp B s = P1.cost inp B s + ((bitEvalW g).cost inp B t1 +
        ((seqs [ar .mul (g + 36) (g + 24) (g + 27), ar .add (g + 36) (g + 36) (g + 19)]).cost
          inp B t2 + 0)) := rfl
    rw [hc]
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_ar, exec_seqs_cons, exec_ar,
      arith_mul, HS.setR_regs, upd_ne, upd_eq, w24, w27, b1]
    have := kappa_bits_le B (a := Q + α) (M := Ms) (by omega)
    have := kappa_bits_le B (a := Q * α + bitEval Q p K id α) (M := Ms) (by omega)
    have e : (K * (36 * W + 24) + 8) * kappa B (RAM.bits Ms) =
      2 * kappa B (RAM.bits Ms) + (K * (36 * W + 24) + 4) * kappa B (RAM.bits Ms) +
        2 * kappa B (RAM.bits Ms) := by ring
    omega


end Out

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.colorOut_spec_oai := @EditMulticoloring.Dev.Ram.colorOut_spec_oai
