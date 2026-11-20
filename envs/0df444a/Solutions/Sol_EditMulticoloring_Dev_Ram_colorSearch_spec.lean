-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.colorSearch_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:41.706174+00:00
-- url     : https://prove2.me/submissions/39d96221-dff7-4124-b484-a616fead80c8

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_gfField_spec
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

section Search
variable (inp : ℕ → ℕ) (B : ℕ)

theorem nLoop_spec (g : ℕ) (s : HS) (p W Q K J DG Ms : ℕ) (ids : ℕ → ℕ) (a : ℕ)
    (hctx : GFCtx s g p W) (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (h7 : s.regs (g + 7) = a) (haQ : a < Q) (h16 : s.regs (g + 16) = DG) (h18 : s.regs (g + 18) = K)
    (h26 : s.regs (g + 26) = J) (h29 : s.regs (g + 29) = 1)
    (h30 : s.regs (g + 30) = bitEval Q p K (ids 0) a) (hrows : Rows s DG K Q J ids)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (J + 2) * K + J ≤ Ms) :
    let st' := (forLoop (g + 32) (g + 26) (g + 35) (nBody g)).exec inp s
    st'.regs (g + 29) = (if okAt Q p K ids J a then 1 else 0) ∧
    (∀ r, KeepN g r → st'.regs r = s.regs r) ∧ st'.mem = s.mem ∧
    (forLoop (g + 32) (g + 26) (g + 35) (nBody g)).cost inp B s ≤
      (J * (K * (36 * W + 24) + 15) + 3) * kappa B (RAM.bits Ms) := by
  intro st'
  set e0 := bitEval Q p K (ids 0) a with he0
  set f := fun j => bitEval Q p K (ids 0) a != bitEval Q p K (ids (j + 1)) a with hf
  have hWW : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbe : ∀ m, bitEval Q p K (ids m) a < 2 ^ W := by
    intro m
    unfold bitEval
    have : ∀ (l : List ℕ) z, z < 2 ^ W → l.foldl (fun z i =>
        Nat.xor (fieldMul p z a) ((ids m / Q ^ i) % Q)) z < 2 ^ W := by
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
  have KL := forLoop_spec inp B (g + 32) (g + 26) (g + 35) (nBody g) s (by omega) (by omega)
    (fun j st => st.regs (g + 29) = (if (List.range j).all f then 1 else 0) ∧
      (∀ r, KeepN g r → st.regs r = s.regs r) ∧ st.mem = s.mem)
    (fun _ => (K * (36 * W + 24) + 12) * kappa B (RAM.bits Ms))
    ⟨by simp (disch := omega) [upd_ne, h29], fun r h => by
      unfold KeepN at h; simp (disch := omega) [upd_ne], by simp⟩
    (by
      intro j hj st ⟨hok, hr, hm⟩ hjj
      rw [h26] at hj
      have kr : ∀ r, KeepN g r → st.regs r = s.regs r := hr
      set P1 := seqs [lit (g + 34) 1, ar .add (g + 34) (g + 32) (g + 34),
        ar .mul (g + 17) (g + 34) (g + 18)] with hP1
      set s1 := P1.exec inp st with hs1
      have r1 : ∀ r, (r ≠ g + 34 ∧ r ≠ g + 17) → s1.regs r = st.regs r := by
        intro r hr; simp (disch := omega) [hs1, hP1, upd_ne]
      have k18 : st.regs (g + 18) = K := by rw [kr _ (by unfold KeepN; omega), h18]
      have v17 : s1.regs (g + 17) = (j + 1) * K := by
        simp (disch := omega) [hs1, hP1, upd_ne, hjj, k18]
      have m1 : s1.mem = s.mem := by simp [hs1, hP1, hm]
      have c1 : P1.cost inp B st ≤ 3 * kappa B (RAM.bits Ms) := by
        simp (disch := omega) only [hP1, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar,
          exec_seqs_cons, exec_lit, exec_ar, arith_add, HS.setR_regs, upd_ne, upd_eq, hjj, k18]
        have : (j + 1) * K + K ≤ (J + 2) * K := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
        have := kappa_bits_le B (a := 1) (M := Ms) (by omega)
        have := kappa_bits_le B (a := j + 1) (M := Ms) (by omega)
        have := kappa_bits_le B (a := j + 1 + K) (M := Ms) (by
          have : K ≤ (j + 1) * K := Nat.le_mul_of_pos_left _ (by omega)
          omega)
        omega
      have ks1 : ∀ r, KeepN g r → s1.regs r = s.regs r := fun r h => by
        rw [r1 r (by unfold KeepN at h; omega), kr r h]
      have hctx1 : GFCtx s1 g p W := hctx.congr (fun r h1 h2 => ks1 r (by unfold KeepN; omega))
      have a1 : s1.regs (g + 7) = a := by rw [ks1 _ (by unfold KeepN; omega), h7]
      have d1 : s1.regs (g + 16) = DG := by rw [ks1 _ (by unfold KeepN; omega), h16]
      have q1 : s1.regs (g + 18) = K := by rw [ks1 _ (by unfold KeepN; omega), h18]
      have hJK : (j + 1) * K + 2 * K ≤ (J + 2) * K := by
        rw [show (j + 1) * K + 2 * K = (j + 3) * K by ring]
        exact Nat.mul_le_mul_right _ (by omega)
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := bitEvalW_spec inp B g s1 p W Q (ids (j + 1)) Ms hctx1 hp hpW
        hQ0 hQW (by rw [a1]; omega)
        (fun i hi => by
          rw [d1, v17]; rw [q1] at hi
          rw [show s1.arr DG ((j + 1) * K + i) = s.arr DG ((j + 1) * K + i) by simp [HS.arr, m1]]
          exact hrows (j + 1) (by omega) i hi)
        (by rw [d1, v17, q1]; omega)
      rw [q1, a1] at b1
      rw [q1] at b6
      set s2 := (bitEvalW g).exec inp s1 with hs2
      have ks2 : ∀ r, KeepN g r → r ≠ g + 6 → s2.regs r = s.regs r := fun r h h6 => by
        rw [b2 r (by unfold BevKeep; unfold KeepN at h; omega), ks1 r h]
      have v30 : s2.regs (g + 30) = e0 := by
        rw [ks2 _ (by unfold KeepN; omega) (by omega), h30]
      have v29 : s2.regs (g + 29) = (if (List.range j).all f then 1 else 0) := by
        rw [b2 _ (by unfold BevKeep; omega), r1 _ (by omega), hok]
      have m2 : s2.mem = s.mem := by rw [b3, m1]
      set e1 := bitEval Q p K (ids (j + 1)) a with he1
      have hex : (nBody g).exec inp st = (seqs [ar .sub (g + 34) (g + 30) (g + 19),
          ar .sub (g + 36) (g + 19) (g + 30), ar .add (g + 34) (g + 34) (g + 36),
          .ifz (g + 34) (lit (g + 29) 0) .skip]).exec inp s2 := rfl
      have hcost : (nBody g).cost inp B st = P1.cost inp B st + ((bitEvalW g).cost inp B s1 +
          ((seqs [ar .sub (g + 34) (g + 30) (g + 19),
          ar .sub (g + 36) (g + 19) (g + 30), ar .add (g + 34) (g + 34) (g + 36),
          .ifz (g + 34) (lit (g + 29) 0) .skip]).cost inp B s2 + 0)) := rfl
      have hstep : (List.range (j + 1)).all f = ((List.range j).all f && (e0 != e1)) := by
        rw [List.range_succ, List.all_append]; simp [hf, he0, he1]
      have E0 := hbe 0
      have E1 := hbe (j + 1)
      have K1 := kappa_bits_le B (a := e0 + e1) (M := Ms) (by omega)
      have K2 := kappa_bits_le B (a := e1 + e0) (M := Ms) (by omega)
      have K3 := kappa_bits_le B (a := e0 - e1 + (e1 - e0)) (M := Ms) (by omega)
      have K4 := kappa_bits_le B (a := 0) (M := Ms) (by omega)
      rw [hex, hcost]
      by_cases hd : e0 - e1 + (e1 - e0) = 0
      · have he : e0 = e1 := by omega
        simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_lit,
          arith_sub, arith_add, HS.setR_regs, upd_ne, upd_eq, v30, b1, hd, if_true,
          cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_lit]
        refine ⟨by rw [b2 _ (by unfold BevKeep; omega), r1 _ (by omega), hjj], ⟨?_, ?_, ?_⟩, ?_⟩
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs])
          rw [hstep, he]; simp
        · intro r h
          unfold KeepN at h
          simp (disch := omega) only [upd_ne, HS.setR_regs]
          exact ks2 r (by unfold KeepN; omega) (by omega)
        · simpa using m2
        · have : (K * (36 * W + 24) + 12) * kappa B (RAM.bits Ms) = 3 * kappa B (RAM.bits Ms) + (K * (36 * W + 24) + 4) * kappa B (RAM.bits Ms) + 5 * kappa B (RAM.bits Ms) := by ring
          omega
      · have he : e0 ≠ e1 := by omega
        simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz, exec_lit,
          exec_skip, arith_sub, arith_add, HS.setR_regs, upd_ne, upd_eq, v30, b1, hd, if_false,
          cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_lit, cost_skip]
        refine ⟨by rw [b2 _ (by unfold BevKeep; omega), r1 _ (by omega), hjj], ⟨?_, ?_, ?_⟩, ?_⟩
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs])
          rw [v29, hstep]; simp [he]
        · intro r h
          unfold KeepN at h
          simp (disch := omega) only [upd_ne, HS.setR_regs]
          exact ks2 r (by unfold KeepN; omega) (by omega)
        · simpa using m2
        · have : (K * (36 * W + 24) + 12) * kappa B (RAM.bits Ms) = 3 * kappa B (RAM.bits Ms) + (K * (36 * W + 24) + 4) * kappa B (RAM.bits Ms) + 5 * kappa B (RAM.bits Ms) := by ring
          omega)
  rw [h26] at KL
  obtain ⟨⟨k1, k2, k3⟩, k4⟩ := KL
  refine ⟨by rw [k1]; rfl, k2, k3, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
  have := kappa_bits_le B (a := J) (M := Ms) (by omega)
  have e : (J * (K * (36 * W + 24) + 15) + 3) * kappa B (RAM.bits Ms) = 3 * (J + 1) * kappa B (RAM.bits Ms) + J * ((K * (36 * W + 24) + 12) * kappa B (RAM.bits Ms)) := by ring
  rw [e]
  refine k4.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _)


theorem find_range_succ (P : ℕ → Bool) (a : ℕ) :
    (List.range (a + 1)).find? P = ((List.range a).find? P).or (if P a then some a else none) := by
  rw [List.range_succ, List.find?_append]
  simp only [List.find?_cons, List.find?_nil]
  cases P a <;> simp

theorem colorSearch_spec_oai (g : ℕ) (s : HS) (p W Q K J DG Ms : ℕ) (ids : ℕ → ℕ)
    (hctx : GFCtx s g p W) (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (h16 : s.regs (g + 16) = DG) (h18 : s.regs (g + 18) = K) (h24 : s.regs (g + 24) = Q)
    (h26 : s.regs (g + 26) = J) (hrows : Rows s DG K Q J ids)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (J + 2) * K + J ≤ Ms) :
    let st' := (colorSearch g).exec inp s
    st'.regs (g + 27) = ((List.range Q).find? (okAt Q p K ids J)).getD 0 ∧
    (∀ r, KeepS g r → st'.regs r = s.regs r) ∧ st'.mem = s.mem ∧
    (colorSearch g).cost inp B s ≤
      (Q * ((J + 1) * (K * (36 * W + 24) + 15)) + 3 * Q + 5) * kappa B (RAM.bits Ms) := by
  intro st'
  set F := fun a => (List.range a).find? (okAt Q p K ids J) with hF
  set X := K * (36 * W + 24) with hX
  have hWW : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set s1 := (seqs [lit (g + 27) 0, lit (g + 28) 0]).exec inp s with hs1
  have hn1 : s1.regs (g + 24) = Q := by simp (disch := omega) [hs1, upd_ne, h24]
  have KL := forLoop_spec inp B (g + 31) (g + 24) (g + 33) (sBody g) s1 (by omega) (by omega)
    (fun a st => st.regs (g + 28) = (if (F a).isSome then 1 else 0) ∧ st.regs (g + 27) = (F a).getD 0 ∧
      (∀ r, KeepS g r → st.regs r = s.regs r) ∧ st.mem = s.mem)
    (fun _ => (J + 1) * (X + 15) * kappa B (RAM.bits Ms))
    ⟨by simp (disch := omega) [hs1, upd_ne, hF], by simp (disch := omega) [hs1, upd_ne, hF],
      fun r h => by unfold KeepS at h; simp (disch := omega) [hs1, upd_ne], by simp [hs1]⟩
    (by
      intro a ha st ⟨hfd, hal, hr, hm⟩ hj
      rw [hn1] at ha
      have hK : ∀ r, KeepS g r → st.regs r = s.regs r := hr
      set P1 := seqs [cp (g + 7) (g + 31), lit (g + 17) 0] with hP1
      set t1 := P1.exec inp st with ht1
      have r1 : ∀ r, (r ≠ g + 7 ∧ r ≠ g + 17) → t1.regs r = st.regs r := by
        intro r hr; simp (disch := omega) [ht1, hP1, upd_ne]
      have m1 : t1.mem = s.mem := by simp [ht1, hP1, hm]
      have v7 : t1.regs (g + 7) = a := by simp (disch := omega) [ht1, hP1, upd_ne, hj]
      have v17 : t1.regs (g + 17) = 0 := by simp (disch := omega) [ht1, hP1, upd_ne]
      have c1 : P1.cost inp B st ≤ 2 * kappa B (RAM.bits Ms) := by
        simp (disch := omega) only [hP1, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
          exec_seqs_cons, exec_cp, HS.setR_regs, upd_ne, upd_eq, hj]
        have := kappa_bits_le B (a := a) (M := Ms) (by omega)
        have := kappa_bits_le B (a := 0) (M := Ms) (by omega)
        omega
      have kt1 : ∀ r, KeepS g r → t1.regs r = s.regs r := fun r h => by
        rw [r1 r (by unfold KeepS at h; omega), hK r h]
      have hctx1 : GFCtx t1 g p W := hctx.congr (fun r h1 h2 => kt1 r (by unfold KeepS; omega))
      have d1 : t1.regs (g + 16) = DG := by rw [kt1 _ (by unfold KeepS; omega), h16]
      have q1 : t1.regs (g + 18) = K := by rw [kt1 _ (by unfold KeepS; omega), h18]
      obtain ⟨b1, b2, b3, -, -, b6⟩ := bitEvalW_spec inp B g t1 p W Q (ids 0) Ms hctx1 hp hpW
        hQ0 hQW (by rw [v7]; omega)
        (fun i hi => by
          rw [d1, v17]; rw [q1] at hi
          rw [show t1.arr DG (0 + i) = s.arr DG (0 * K + i) by simp [HS.arr, m1]]
          exact hrows 0 (by omega) i hi)
        (by rw [d1, v17, q1]; have : 2 * K ≤ (J + 2) * K := Nat.mul_le_mul_right _ (by omega)
            omega)
      rw [q1, v7] at b1
      rw [q1] at b6
      set t2 := (bitEvalW g).exec inp t1 with ht2
      set e0 := bitEval Q p K (ids 0) a with he0
      have kt2 : ∀ r, KeepS g r → t2.regs r = s.regs r := fun r h => by
        rw [b2 r (by unfold BevKeep; unfold KeepS at h; omega), kt1 r h]
      set P3 := seqs [cp (g + 30) (g + 19), lit (g + 29) 1] with hP3
      set t3 := P3.exec inp t2 with ht3
      have r3 : ∀ r, (r ≠ g + 30 ∧ r ≠ g + 29) → t3.regs r = t2.regs r := by
        intro r hr; simp (disch := omega) [ht3, hP3, upd_ne]
      have m3 : t3.mem = s.mem := by simp [ht3, hP3, b3, m1]
      have hE : e0 < 2 ^ W := bitEval_lt Q p K W (ids 0) a hp hpW hQ0 hQW
      have c3 : P3.cost inp B t2 ≤ 2 * kappa B (RAM.bits Ms) := by
        simp (disch := omega) only [hP3, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
          exec_seqs_cons, exec_cp, HS.setR_regs, upd_ne, upd_eq, b1]
        have := kappa_bits_le B (a := e0) (M := Ms) (by omega)
        have := kappa_bits_le B (a := 1) (M := Ms) (by omega)
        omega
      have kt3 : ∀ r, KeepS g r → t3.regs r = s.regs r := fun r h => by
        rw [r3 r (by unfold KeepS at h; omega), kt2 r h]
      have w7 : t3.regs (g + 7) = a := by
        rw [r3 _ (by omega), b2 _ (by unfold BevKeep; omega), v7]
      have w31 : t3.regs (g + 31) = a := by
        rw [r3 _ (by omega), b2 _ (by unfold BevKeep; omega), r1 _ (by omega), hj]
      have w27 : t3.regs (g + 27) = (F a).getD 0 := by
        rw [r3 _ (by omega), b2 _ (by unfold BevKeep; omega), r1 _ (by omega), hal]
      have w28 : t3.regs (g + 28) = (if (F a).isSome then 1 else 0) := by
        rw [r3 _ (by omega), b2 _ (by unfold BevKeep; omega), r1 _ (by omega), hfd]
      obtain ⟨n1, n2, n3, n4⟩ := nLoop_spec inp B g t3 p W Q K J DG Ms ids a
        (hctx.congr (fun r h1 h2 => kt3 r (by unfold KeepS; omega))) hp hpW hQ0 hQW w7 ha
        (by rw [kt3 _ (by unfold KeepS; omega), h16]) (by rw [kt3 _ (by unfold KeepS; omega), h18])
        (by rw [kt3 _ (by unfold KeepS; omega), h26]) (by simp (disch := omega) [ht3, hP3, upd_ne])
        (by simp (disch := omega) [ht3, hP3, upd_ne, b1, he0])
        (fun m hm i hi => by rw [show t3.arr DG (m * K + i) = s.arr DG (m * K + i) by
          simp [HS.arr, m3]]; exact hrows m hm i hi) hMs
      set t4 := (forLoop (g + 32) (g + 26) (g + 35) (nBody g)).exec inp t3 with ht4
      have u28 : t4.regs (g + 28) = (if (F a).isSome then 1 else 0) := by
        rw [n2 _ (by unfold KeepN; omega), w28]
      have u27 : t4.regs (g + 27) = (F a).getD 0 := by rw [n2 _ (by unfold KeepN; omega), w27]
      have u31 : t4.regs (g + 31) = a := by rw [n2 _ (by unfold KeepN; omega), w31]
      have kt4 : ∀ r, KeepS g r → t4.regs r = s.regs r := fun r h => by
        rw [n2 r (by unfold KeepN; unfold KeepS at h; omega), kt3 r h]
      have m4 : t4.mem = s.mem := by rw [n3, m3]
      have hex : (sBody g).exec inp st = (Cmd.ifz (g + 28) (.ifz (g + 29) .skip
          (seqs [lit (g + 28) 1, cp (g + 27) (g + 31)])) .skip).exec inp t4 := rfl
      have hcost : (sBody g).cost inp B st = P1.cost inp B st + ((bitEvalW g).cost inp B t1 +
          (P3.cost inp B t2 + ((forLoop (g + 32) (g + 26) (g + 35) (nBody g)).cost inp B t3 +
          ((Cmd.ifz (g + 28) (.ifz (g + 29) .skip
          (seqs [lit (g + 28) 1, cp (g + 27) (g + 31)])) .skip).cost inp B t4 + 0)))) := rfl
      have hstep := find_range_succ (okAt Q p K ids J) a
      have hcostE : ∀ c, c ≤ 4 * kappa B (RAM.bits Ms) → P1.cost inp B st +
          ((bitEvalW g).cost inp B t1 + (P3.cost inp B t2 +
          ((forLoop (g + 32) (g + 26) (g + 35) (nBody g)).cost inp B t3 + (c + 0)))) ≤
          (J + 1) * (X + 15) * kappa B (RAM.bits Ms) := by
        intro c hc
        have : (J + 1) * (X + 15) * kappa B (RAM.bits Ms) = 2 * kappa B (RAM.bits Ms) +
          (K * (36 * W + 24) + 4) * kappa B (RAM.bits Ms) + 2 * kappa B (RAM.bits Ms) +
          (J * (K * (36 * W + 24) + 15) + 3) * kappa B (RAM.bits Ms) + 4 * kappa B (RAM.bits Ms) := by
          rw [hX]; ring
        omega
      have K0 := kappa_bits_le B (a := 0) (M := Ms) (by omega)
      have K1 := kappa_bits_le B (a := 1) (M := Ms) (by omega)
      have Ka := kappa_bits_le B (a := a) (M := Ms) (by omega)
      rw [hex, hcost]
      rcases hFa : F a with _ | v
      · -- not found yet
        have hFa' : (List.range a).find? (okAt Q p K ids J) = none := hFa
        rw [hFa] at u28 u27
        simp only [Option.isSome_none, Bool.false_eq_true, if_false] at u28
        by_cases hok : okAt Q p K ids J a = true
        · have hF1 : F (a + 1) = some a := by
            show (List.range (a + 1)).find? _ = _
            rw [hstep, hFa', hok]; rfl
          rw [hok, if_pos rfl] at n1
          simp (disch := omega) only [exec_ifz, u28, n1, if_true, one_ne_zero, if_false,
            exec_seqs_cons, exec_seqs_nil, exec_lit, exec_cp, HS.setR_regs, upd_ne, upd_eq, u31,
            cost_ifz, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp]
          refine ⟨by simp (disch := omega) [upd_ne, u31], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
          · (try simp (disch := omega) only [upd_ne, upd_eq]); rw [hF1]; (try rfl)
          · (try simp (disch := omega) only [upd_ne, upd_eq]); rw [hF1]; (try rfl)
          · intro r h; unfold KeepS at h
            simp (disch := omega) only [upd_ne]; exact kt4 r (by unfold KeepS; omega)
          · simpa using m4
          · apply hcostE; omega
        · have hok' : okAt Q p K ids J a = false := by simpa using hok
          have hF1 : F (a + 1) = none := by
            show (List.range (a + 1)).find? _ = _
            rw [hstep, hFa', hok']; rfl
          rw [hok', if_neg (by simp)] at n1
          simp (disch := omega) only [exec_ifz, u28, n1, if_true, exec_skip,
            cost_ifz, cost_skip]
          refine ⟨by rw [u31], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hF1, u28]; (try rfl)
          · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hF1, u27]; (try rfl)
          · intro r h; unfold KeepS at h
            simp (disch := omega) only [upd_ne, HS.setR_regs]; exact kt4 r (by unfold KeepS; omega)
          · simpa using m4
          · apply hcostE; omega
      · -- already found
        have hFa' : (List.range a).find? (okAt Q p K ids J) = some v := hFa
        have hF1 : F (a + 1) = some v := by
          show (List.range (a + 1)).find? _ = _
          rw [hstep, hFa']; rfl
        rw [hFa] at u28 u27
        simp only [Option.isSome_some, if_true] at u28
        simp (disch := omega) only [exec_ifz, u28, one_ne_zero, if_false, exec_skip,
          cost_ifz, cost_skip]
        refine ⟨by rw [u31], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hF1, u28]; (try rfl)
        · (try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs]); rw [hF1, u27]; (try rfl)
        · intro r h; unfold KeepS at h
          simp (disch := omega) only [upd_ne, HS.setR_regs]; exact kt4 r (by unfold KeepS; omega)
        · simpa using m4
        · apply hcostE; omega)
  rw [hn1] at KL
  obtain ⟨⟨-, k2, k3, k4⟩, k5⟩ := KL
  have hex : st' = (forLoop (g + 31) (g + 24) (g + 33) (sBody g)).exec inp s1 := rfl
  refine ⟨by rw [hex, k2], fun r h => by rw [hex, k3 r h], by rw [hex, k4], ?_⟩
  have hc : (colorSearch g).cost inp B s = kappa B (RAM.bits 0) + (kappa B (RAM.bits 0) +
      ((forLoop (g + 31) (g + 24) (g + 33) (sBody g)).cost inp B s1 + 0)) := rfl
  rw [hc]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k5
  have hQ2 : Q ≤ 2 ^ (2 * W) := le_trans hQW hWW
  have hκQ := kappa_bits_le B (a := Q) (M := Ms) (by omega)
  have := kappa_bits_le B (a := 0) (M := Ms) (by omega)
  have e : (Q * ((J + 1) * (K * (36 * W + 24) + 15)) + 3 * Q + 5) * kappa B (RAM.bits Ms) =
      2 * kappa B (RAM.bits Ms) + (3 * (Q + 1) * kappa B (RAM.bits Ms) +
        Q * ((J + 1) * (X + 15) * kappa B (RAM.bits Ms))) := by rw [hX]; ring
  rw [e]
  have h3 : 3 * (Q + 1) * kappa B (RAM.bits Q) ≤ 3 * (Q + 1) * kappa B (RAM.bits Ms) :=
    Nat.mul_le_mul_left _ hκQ
  omega

end Search

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.colorSearch_spec_oai := @EditMulticoloring.Dev.Ram.colorSearch_spec_oai
