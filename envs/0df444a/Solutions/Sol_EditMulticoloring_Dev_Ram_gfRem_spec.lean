-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.gfRem_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:52.137186+00:00
-- url     : https://prove2.me/submissions/4eca473e-92af-404b-bf9a-fd5dc5664de7

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
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

theorem p_lt_pow (p : ℕ) : p < 2 ^ (p.log2 + 1) := Nat.lt_log2_self

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

theorem gfRem_spec_oai (g : ℕ) (s : HS) (M : ℕ) (hp : s.regs g ≠ 0)
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


/-! ## `bitEval` on a digit array -/

end Prog

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.gfRem_spec_oai := @EditMulticoloring.Dev.Ram.gfRem_spec_oai
