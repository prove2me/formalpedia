-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EnumCfg.repPhase
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:37.673017+00:00
-- url     : https://prove2.me/submissions/e80394c7-205b-4991-8b9e-a98cedb55828

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
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

/-- The sum identity used to turn per-iteration list costs into a list length. -/
theorem sum_range_flatMap_length {β : Type*} (G : ℕ → List β) (X D N : ℕ) :
    ∑ k ∈ Finset.range N, ((G k).length * X + D) =
      ((List.range N).flatMap G).length * X + N * D := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    ring

/-- The for-loop lemma in list-fold form: iteration `k` folds `f` over the list `G k`, and
costs at most `(G k).length * X + D`.  The step may use that the current accumulator is the
fold over the earlier iterations. -/
theorem forLoop_fold {α β : Type*} (i n one : ℕ) (body : Cmd) (s : HS) (hni : n ≠ i)
    (hio : i ≠ one) (G : ℕ → List β) (f : α → β → α) (Q : α → HS → Prop) (X D : ℕ) (acc : α)
    (h0 : Q acc (s.setR i 0))
    (hstep : ∀ k < s.regs n, ∀ a st, Q a st →
      a = ((List.range k).flatMap G).foldl f acc → st.regs i = k →
      (body.exec inp st).regs i = k ∧
      Q ((G k).foldl f a) (((body.exec inp st).setR one 1).setR i (k + 1)) ∧
      body.cost inp B st ≤ (G k).length * X + D) :
    Q (((List.range (s.regs n)).flatMap G).foldl f acc) ((forLoop i n one body).exec inp s) ∧
    (forLoop i n one body).cost inp B s ≤
      ((List.range (s.regs n)).flatMap G).length * X + s.regs n * D +
        3 * (s.regs n + 1) * kappa B (RAM.bits (s.regs n)) := by
  have := forLoop_spec inp B i n one body s hni hio
    (fun k st => Q (((List.range k).flatMap G).foldl f acc) st) (fun k => (G k).length * X + D)
    (by simpa using h0) (by
      intro k hk st hQ hi
      obtain ⟨h1, h2, h3⟩ := hstep k hk _ st hQ rfl hi
      refine ⟨h1, ?_, h3⟩
      simp only [List.range_succ, List.flatMap_append, List.foldl_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact h2)
  rw [sum_range_flatMap_length] at this
  exact ⟨this.1, by linarith [this.2]⟩

end Loops

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator (q379, Part L)

`enumScripts q s cfg body` runs `body` once per element of `visits s x` (in list order), each
time with the visited word in array `cfg.vis` (offset 0) and its length in register `cfg.VL`.
Main theorem: `enumScripts_spec` (RamEnum3.lean); level induction in RamEnum2.lean.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The visit list -/

theorem repW_length {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) (hi : i < x.length) :
    (repW x i a).length = x.length := by
  simp [repW]; omega

theorem repW_get_ne {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) (hi : i < x.length) (j : ℕ)
    (hj : j ≠ i) (h : j < (repW x i a).length) :
    (repW x i a)[j] = x[j]'(by simp [repW] at h; omega) := by
  simp only [repW]
  rcases Nat.lt_or_gt_of_ne hj with hj | hj
  · rw [List.getElem_append_left (by simp <;> omega)]
    simp
  · rw [List.getElem_append_right (by simp <;> omega)]
    simp only [List.length_take, Nat.min_eq_left hi.le]
    obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - i - 1, by omega⟩
    simp [show i + 1 + m - i = m + 1 by omega]
theorem repW_get_eq {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) (hi : i < x.length)
    (h : i < (repW x i a).length) : (repW x i a)[i] = a := by
  simp only [repW]
  rw [List.getElem_append_right (by simp <;> omega)]
  simp [Nat.min_eq_left hi.le]

/-! ## Configuration -/

namespace EnumCfg
variable (c : EnumCfg)

theorem Agree.setR {s r : ℕ} (hr : c.ownsReg s r) (st : HS) (v : ℕ) : c.Agree s st (st.setR r v) :=
  ⟨fun r' hr' => by
      have : r' ≠ r := fun h => hr' (h ▸ hr)
      simp [Function.update_of_ne this], fun _ _ _ => rfl, rfl, rfl⟩

theorem Fr.agree {s w Y : ℕ} {st st' : HS} (h : c.Fr w Y st st') (hw : c.ownsReg s w)
    (hY : c.ownsArr s Y) : c.Agree s st st' := by
  refine ⟨fun r hr => h.1 r ?_ ?_, fun y i hy => h.2.1 y i ?_, h.2.2.1, h.2.2.2⟩
  · simp only [ownsReg, not_and, not_le] at hr; omega
  · rintro rfl; exact hr hw
  · rintro rfl; exact hy hY

/-! ## Code -/

end EnumCfg

/-! ## Specs of the pieces -/

namespace EnumCfg
variable (c : EnumCfg) (inp : ℕ → ℕ) (B : ℕ)

theorem cpy_run (st : HS) (vS vso vD vdo N V M : ℕ) (h1 : st.regs c.S = vS)
    (h2 : st.regs c.so = vso) (h3 : st.regs c.D = vD) (h4 : st.regs c.dO = vdo)
    (h5 : st.regs c.n = N) (hSD : vS ≠ vD) (hV : ∀ i < N, st.arr vS (vso + i) ≤ V)
    (hM : vS + vso + vD + vdo + N + V ≤ M) :
    (∀ i < N, (c.cpy.exec inp st).arr vD (vdo + i) = st.arr vS (vso + i)) ∧
    (∀ y i, ¬ (y = vD ∧ vdo ≤ i ∧ i < vdo + N) → (c.cpy.exec inp st).arr y i = st.arr y i) ∧
    (∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r ∨ r = c.S ∨ r = c.so ∨ r = c.D ∨ r = c.dO ∨ r = c.n ∨
        r = c.d ∨ r = c.e ∨ r = c.cnt ∨ r = c.VL) →
      (c.cpy.exec inp st).regs r = st.regs r) ∧
    (c.cpy.exec inp st).cur = st.cur ∧ (c.cpy.exec inp st).out = st.out ∧
    c.cpy.cost inp B st ≤ (7 * N + 3) * kappa B (RAM.bits M) := by
  have hreg : [c.S, c.so, c.D, c.dO, c.n, c.j, c.t, c.u, c.one].Nodup := by
    simp [List.nodup_cons]
  have := copyW_spec inp B c.S c.so c.D c.dO c.n c.j c.t c.u c.one st hreg
    (by rw [h1, h3]; exact hSD) V M (by rw [h1, h2, h5]; exact hV)
    (by rw [h1, h2, h3, h4, h5]; exact hM)
  rw [h1, h2, h3, h4, h5] at this
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := this
  refine ⟨a1, a2, fun r hr => a3 r ?_ ?_ ?_ ?_, a4, a5, a6⟩ <;>
    · simp only [S, so, D, dO, n, j, t, u, one, d, e, cnt, VL] at hr ⊢; omega

theorem repC_spec {q : ℕ} (k : ℕ) (x : Word q) (st : HS) (i : ℕ) (a : Fin q) (hi : i < x.length)
    (hlen : st.regs (c.lenR (k + 1)) = x.length) (hx : WordAt st (c.buf (k + 1)) 0 x)
    (hiR : st.regs (c.iR (k + 1)) = i) (haR : st.regs (c.aR (k + 1)) = a.val)
    (M : ℕ) (hM : 2 * c.a0 + 2 * x.length + 2 * k + q + 4 ≤ M) :
    ((c.repC k).exec inp st).regs (c.lenR k) = (repW x i a).length ∧
    WordAt ((c.repC k).exec inp st) (c.buf k) 0 (repW x i a) ∧
    c.Fr (c.lenR k) (c.buf k) st ((c.repC k).exec inp st) ∧
    (c.repC k).cost inp B st ≤ (7 * x.length + 20) * kappa B (RAM.bits M) := by
  simp only [lenR, iR, aR] at hlen hiR haR
  have xlt := hx.lt
  have hx' : ∀ j (h : j < x.length), st.arr (c.buf (k + 1)) j = (x[j]).val := fun j h => by
    simpa using hx j h
  set s1 := (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
    cp c.n (c.lenR (k + 1))]).exec inp st with hs1
  have e1 : ∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r) → s1.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs1]
  have m1 : ∀ y j, s1.arr y j = st.arr y j := by intro y j; simp [hs1]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := c.cpy_run inp B s1 (c.buf (k + 1)) 0 (c.buf k) 0 x.length
    q M (by simp [hs1]) (by simp [hs1]) (by simp [hs1]) (by simp [hs1])
    (by simp (disch := omega) [hs1, hlen]) (by simp <;> omega)
    (fun j hj => by rw [m1]; exact (xlt j (by omega)).le) (by simp <;> omega)
  set s2 := c.cpy.exec inp s1 with hs2
  have r2 : ∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r) → s2.regs r = st.regs r := fun r hr =>
    (a3 r (hr.elim Or.inl (fun h => Or.inr (Or.inl h)))).trans (e1 r hr)
  have r2D : s2.regs (c.r0 + 5) = c.a0 + 1 + k := by
    rw [a3 _ (by simp)]; simp [hs1]
  have a1' : ∀ j < x.length, s2.arr (c.buf k) j = s1.arr (c.buf (k + 1)) j := fun j h => by
    simpa using a1 j h
  have hiR2 : s2.regs (c.r0 + (16 + 3 * (k + 1))) = i := by rw [r2 _ (by omega)]; exact hiR
  have haR2 : s2.regs (c.r0 + (17 + 3 * (k + 1))) = a.val := by rw [r2 _ (by omega)]; exact haR
  have hlen2 : s2.regs (c.r0 + (18 + 3 * (k + 1))) = x.length := by rw [r2 _ (by omega)]; exact hlen
  have hex : (c.repC k).exec inp st =
      (seqs [ast c.D (c.iR (k + 1)) (c.aR (k + 1)), cp (c.lenR k) (c.lenR (k + 1))]).exec inp s2 :=
    rfl
  rw [hex]
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (disch := omega) [hlen2, repW_length x i a hi, r2D, hiR2]
  · intro j hj
    rw [repW_length x i a hi] at hj
    simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ast, exec_cp, HS.setR_arr,
      HS.store_arr, Nat.zero_add, D, iR, aR, r2D, hiR2, haR2]
    by_cases hji : j = i
    · subst hji; simp [repW_get_eq x j a hi]
    · rw [if_neg (by simp; omega), a1' j hj, m1, hx' j hj, repW_get_ne x i a hi j hji]
  · intro r hr hrw
    simp only [lenR] at hrw
    simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ast, exec_cp, HS.setR_regs,
      HS.store_regs, upd_ne, lenR]
    exact r2 r hr
  · intro y j hy
    simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ast, exec_cp, HS.setR_arr,
      HS.store_arr, D, r2D]
    simp only [buf] at hy
    rw [if_neg (by omega), a2 _ _ (by simp <;> omega), m1]
  · simp [a4, hs1]
  · simp [a5, hs1]
  · have hc : (c.repC k).cost inp B st =
        (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
          cp c.n (c.lenR (k + 1))]).cost inp B st + c.cpy.cost inp B s1 +
        (seqs [ast c.D (c.iR (k + 1)) (c.aR (k + 1)), cp (c.lenR k) (c.lenR (k + 1))]).cost
          inp B s2 := by
      simp only [repC, cost_seq]; ring
    rw [hc]
    have K0 := kappa_bits_le B (a := 0) (M := M) (by omega)
    have p1 : (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
          cp c.n (c.lenR (k + 1))]).cost inp B st ≤ 5 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons,
        exec_lit, HS.setR_regs, upd_ne, lenR, S, so, D, dO, hlen, buf]
      have := kappa_bits_le B (a := c.a0 + 1 + (k + 1)) (M := M) (by omega)
      have := kappa_bits_le B (a := c.a0 + 1 + k) (M := M) (by omega)
      have := kappa_bits_le B (a := x.length) (M := M) (by omega)
      omega
    have p2 : (seqs [ast c.D (c.iR (k + 1)) (c.aR (k + 1)), cp (c.lenR k) (c.lenR (k + 1))]).cost
          inp B s2 ≤ 2 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_cp, cost_ast,
        exec_seqs_cons, exec_ast, HS.store_regs, iR, aR, lenR, D, r2D, hiR2, haR2, hlen2]
      have := kappa_bits_le B (a := c.a0 + 1 + k + i + a.val) (M := M) (by omega)
      have := kappa_bits_le B (a := x.length) (M := M) (by omega)
      omega
    have h8 : (7 * x.length + 20) * kappa B (RAM.bits M) =
        (7 * x.length + 3) * kappa B (RAM.bits M) + 17 * kappa B (RAM.bits M) := by ring
    omega

theorem neqC_spec {q : ℕ} (k : ℕ) (x : Word q) (st : HS) (i a : ℕ) (hi : i < x.length)
    (ha : a < q) (hx : WordAt st (c.buf (k + 1)) 0 x)
    (hiR : st.regs (c.iR (k + 1)) = i) (haR : st.regs (c.aR (k + 1)) = a)
    (M : ℕ) (hM : 2 * c.a0 + 2 * x.length + 2 * k + 2 * q + 4 ≤ M) :
    (((c.neqC k).exec inp st).regs c.d = 0 ↔ (x[i]).val = a) ∧
    ((c.neqC k).exec inp st).regs c.d ≤ q ∧
    c.Fr (c.lenR k) (c.buf k) st ((c.neqC k).exec inp st) ∧
    (c.neqC k).cost inp B st ≤ 5 * kappa B (RAM.bits M) := by
  simp only [lenR, iR, aR] at hiR haR
  have hx' : st.arr (c.a0 + 1 + (k + 1)) i = (x[i]).val := by simpa using hx i hi
  have hxl : (x[i]).val < q := (x[i]).isLt
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (disch := omega) [neqC, hiR, haR, hx']
    omega
  · simp (disch := omega) [neqC, hiR, haR, hx']
    omega
  · intro r hr _
    simp (disch := omega) [neqC]
  · intro y j _; simp [neqC]
  · simp [neqC]
  · simp [neqC]
  · simp (disch := omega) only [neqC, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ald, cost_ar,
      exec_seqs_cons, exec_lit, exec_ald, exec_ar, HS.setR_regs, HS.setR_arr, upd_ne, upd_eq, S,
      u, d, e, iR, aR, buf, hiR, haR, hx', arith_sub]
    have := kappa_bits_le B (a := c.a0 + 1 + (k + 1)) (M := M) (by omega)
    have := kappa_bits_le B (a := c.a0 + 1 + (k + 1) + i + (x[i]).val) (M := M) (by omega)
    have := kappa_bits_le B (a := (x[i]).val + a) (M := M) (by omega)
    have := kappa_bits_le B (a := a + (x[i]).val) (M := M) (by omega)
    have := kappa_bits_le B (a := (x[i]).val - a + (a - (x[i]).val)) (M := M) (by omega)
    omega

end EnumCfg

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator, part 2: the three edit phases (q379, Part L)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Membership in the visit list -/

/-! ## Positions in the visit list -/

/-- A per-position property of a list fold restricts to a contiguous sublist. -/
theorem ok_sub {α β : Type*} (f : α → β → α) (Ok : α → β → Prop) (a0 : α) (V P W T : List β)
    (hV : V = P ++ W ++ T)
    (hok : ∀ j (hj : j < V.length), Ok ((V.take j).foldl f a0) (V[j])) :
    ∀ j (hj : j < W.length), Ok ((W.take j).foldl f (P.foldl f a0)) (W[j]) := by
  intro j hj
  subst hV
  have h := hok (P.length + j) (by simp; omega)
  have e1 : (P ++ W ++ T).take (P.length + j) = P ++ W.take j := by
    rw [List.append_assoc, List.take_length_add_append, List.take_append_of_le_length (by omega)]
  have e2 : (P ++ W ++ T)[P.length + j]'(by simp; omega) = W[j] := by
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
    simp
  rw [e1, e2, List.foldl_append] at h
  exact h

theorem flatMap_range_split {β : Type*} (G : ℕ → List β) {i n : ℕ} (hi : i < n) :
    ∃ T, (List.range n).flatMap G = (List.range i).flatMap G ++ G i ++ T := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · obtain ⟨T, hT⟩ := ih h
      exact ⟨T ++ G n, by rw [hT]; simp⟩
    · exact ⟨[], by simp⟩

namespace EnumCfg
variable (c : EnumCfg) (inp : ℕ → ℕ) (B : ℕ)

theorem Fr.trans {w Y : ℕ} {st₁ st₂ st₃ : HS} (h₁ : c.Fr w Y st₁ st₂) (h₂ : c.Fr w Y st₂ st₃) :
    c.Fr w Y st₁ st₃ :=
  ⟨fun r h h' => (h₂.1 r h h').trans (h₁.1 r h h'), fun y i h => (h₂.2.1 y i h).trans (h₁.2.1 y i h),
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem ownsReg_of {s r : ℕ} (h1 : c.r0 ≤ r) (h2 : r ≤ c.r0 + (18 + 3 * s)) : c.ownsReg s r :=
  ⟨h1, h2⟩

theorem ownsArr_of {s y : ℕ} (h1 : c.a0 ≤ y) (h2 : y ≤ c.a0 + 1 + s) : c.ownsArr s y :=
  ⟨h1, h2⟩

section Phases
variable {q : ℕ} {α : Type*} (s L : ℕ) (body : Cmd) (Inv : α → HS → Prop) (f : α → Word q → α)
  (cb : ℕ) (Ok : α → Word q → Prop)

theorem LQ.setR (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    {k r : ℕ} (hr : c.ownsReg s r) (hr' : r < c.lenR k) {st0 st : HS} {acc : α}
    (h : c.LQ Inv s k st0 acc st) (v : ℕ) : c.LQ Inv s k st0 acc (st.setR r v) := by
  refine ⟨hstable _ _ _ h.1 (Agree.setR c hr st v), fun r' h1 h2 => ?_, fun y i h1 h2 => h.2.2 y i h1 h2⟩
  have : r' ≠ r := by omega
  simp only [HS.setR_regs, Function.update_of_ne this]
  exact h.2.1 r' h1 h2

/-- After building the child at level `k` (frame `Fr (lenR k) (buf k)`) and running level `k`
(frame `Keep s k`), the levels `≥ k+1` are unchanged. -/
theorem keep_after_child {k : ℕ} {st3 st4 st5 : HS} (h34 : c.Fr (c.lenR k) (c.buf k) st3 st4)
    (h45 : c.Keep s k st4 st5) :
    (∀ r, c.lenR k < r → r ≤ c.lenR s → st5.regs r = st3.regs r) ∧
    (∀ y j, c.buf (k + 1) ≤ y → y ≤ c.buf s → st5.arr y j = st3.arr y j) := by
  refine ⟨fun r h1 h2 => (h45.1 r h1.le h2).trans (h34.1 r (Or.inr ?_) (by omega)),
    fun y j h1 h2 => (h45.2 y j ?_ h2).trans (h34.2.1 y j ?_)⟩
  · simp only [lenR] at h1; omega
  · simp only [buf] at h1 ⊢; omega
  · simp only [buf] at h1 ⊢; omega

theorem getElem?_eq_some_fin {q : ℕ} (x : Word q) (i : ℕ) (hi : i < x.length) (b : Fin q) :
    x[i]? = some b ↔ (x[i]).val = b.val := by
  rw [List.getElem?_eq_getElem hi, Option.some_inj, Fin.ext_iff]

set_option maxHeartbeats 1000000 in
theorem repPhase_oai (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    (k : ℕ) (hk : k + 1 ≤ s) (IH : c.IHk inp B s L body Inv f cb Ok k)
    (x : Word q) (hxL : x.length + (k + 1) ≤ L + s) (a0 : α)
    (hok : ∀ j (hj : j < (visits (k + 1) x).length),
      Ok (((visits (k + 1) x).take j).foldl f a0) ((visits (k + 1) x)[j]))
    (st0 : HS) (hlen0 : st0.regs (c.lenR (k + 1)) = x.length)
    (hx0 : WordAt st0 (c.buf (k + 1)) 0 x) (acc : α) (st : HS)
    (Pre Post : List (Word q))
    (hV : visits (k + 1) x = Pre ++ ((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))) ++ Post)
    (hacc : acc = Pre.foldl f a0)
    (hQ : c.LQ Inv s (k + 1) st0 acc st) (hcnt : st.regs c.cnt = x.length) :
    c.LQ Inv s (k + 1) st0
      (((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))).foldl f acc)
      ((c.repLoop q body k).exec inp st) ∧
    (c.repLoop q body k).cost inp B st ≤
      ((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))).length *
        (cb + c.enumE B q L s) +
      20 * (q + 1) * (x.length + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s)) := by
  set κ := kappa B (RAM.bits (c.enumM q L s)) with hκ
  set E := c.enumE B q L s with hE
  have hM : 2 * c.a0 + 2 * x.length + 2 * k + q + 4 ≤ c.enumM q L s := by
    simp only [enumM]; omega
  have hM' : 2 * c.a0 + 2 * x.length + 2 * k + 2 * q + 4 ≤ c.enumM q L s := by
    simp only [enumM]; omega
  have R := forLoop_fold inp B (c.iR (k + 1)) c.cnt c.one (.seq (lit c.cnt q)
    (forLoop (c.aR (k + 1)) c.cnt c.one (.seq (c.neqC k)
      (.ifz c.d .skip (.seq (c.repC k) (c.lev q body k)))))) st
    (by simp <;> omega) (by simp <;> omega)
    (fun i => (List.range q).flatMap (finFlat fun b =>
      if x[i]? = some b then [] else visits k (repW x i b))) f
    (c.LQ Inv s (k + 1) st0) (cb + E) ((1 + q * (7 * x.length + 26) + 3 * (q + 1)) * κ) acc
    (LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
      (by simp <;> omega) hQ 0)
    (by
      intro i hi acc' st' hQ' hacc' hiR
      rw [hcnt] at hi
      have hc'' : (st'.setR c.cnt q).regs c.cnt = q := by simp
      have R2 := forLoop_fold inp B (c.aR (k + 1)) c.cnt c.one (.seq (c.neqC k)
          (.ifz c.d .skip (.seq (c.repC k) (c.lev q body k))))
        (st'.setR c.cnt q) (by simp <;> omega) (by simp <;> omega)
        (finFlat fun b => if x[i]? = some b then [] else visits k (repW x i b)) f
        (fun a st => c.LQ Inv s (k + 1) st0 a st ∧ st.regs (c.iR (k + 1)) = i)
        (cb + E) ((7 * x.length + 26) * κ) acc'
        ⟨LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
            (by simp <;> omega)
          (LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
            (by simp <;> omega) hQ' q) 0,
          by simp only [HS.setR_regs]
             rw [Function.update_of_ne (by simp <;> omega), Function.update_of_ne (by simp <;> omega)]
             exact hiR⟩
        (by
          intro b hb acc'' st3 ⟨⟨hInv3, hKeep3⟩, hi3⟩ hacc'' hb3
          rw [hc''] at hb
          have hlen3 : st3.regs (c.lenR (k + 1)) = x.length :=
            (hKeep3.1 _ le_rfl (by simp <;> omega)).trans hlen0
          have hx3 : WordAt st3 (c.buf (k + 1)) 0 x :=
            hx0.congr (fun j _ => hKeep3.2 _ _ le_rfl (by simp <;> omega))
          obtain ⟨n1, n2, n3, n4⟩ := c.neqC_spec inp B k x st3 i b hi hb hx3 hi3 hb3 _ hM'
          set st3' := (c.neqC k).exec inp st3 with hst3'
          have hInv3' := hstable _ _ _ hInv3
            (Fr.agree c n3 (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
              (c.ownsArr_of (by simp <;> omega) (by simp <;> omega)))
          have pr : ∀ r, c.lenR k < r → st3'.regs r = st3.regs r := fun r hr =>
            n3.1 r (Or.inr (by simp at hr ⊢ <;> omega)) (by omega)
          have pa : ∀ y j, y ≠ c.buf k → st3'.arr y j = st3.arr y j := fun y j hy => n3.2.1 y j hy
          have e5 : (Cmd.seq (c.neqC k) (.ifz c.d .skip (.seq (c.repC k) (c.lev q body k)))).exec
              inp st3 = (Cmd.ifz c.d .skip (.seq (c.repC k) (c.lev q body k))).exec inp st3' := rfl
          have hd' : (st3'.regs c.d ≤ q) := n2
          by_cases hd : st3'.regs c.d = 0
          · -- symbol equal: nothing visited
            have hxb : x[i]? = some ⟨b, hb⟩ := (getElem?_eq_some_fin x i hi _).mpr (n1.mp hd)
            have hff : finFlat (fun b => if x[i]? = some b then [] else visits k (repW x i b)) b =
                [] := by simp [finFlat, hb, hxb]
            rw [hff, e5]
            simp only [exec_ifz, hd, if_true, exec_skip, List.foldl_nil, List.length_nil, zero_mul,
              zero_add]
            refine ⟨by rw [pr _ (by simp <;> omega)]; exact hb3, ⟨?_, ?_⟩, ?_⟩
            · refine LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
                (by simp <;> omega)
                (LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
                  (by simp <;> omega) ⟨hInv3', fun r h1 h2 => ?_, fun y j h1 h2 => ?_⟩ 1) (b + 1)
              · rw [pr r (by simp at h1 ⊢ <;> omega)]; exact hKeep3.1 r h1 h2
              · rw [pa y j (by simp at h1 ⊢ <;> omega)]; exact hKeep3.2 y j h1 h2
            · simp only [HS.setR_regs]
              rw [Function.update_of_ne (by simp <;> omega), Function.update_of_ne (by simp <;> omega),
                pr _ (by simp <;> omega)]
              exact hi3
            · simp only [cost_seq, cost_ifz]
              rw [← hst3', if_pos hd, hd, cost_skip]
              have := kappa_bits_le B (a := 0) (M := c.enumM q L s) (by omega)
              have h6 : 6 * κ ≤ (7 * x.length + 26) * κ := Nat.mul_le_mul_right _ (by omega)
              omega
          · have hxb : ¬ x[i]? = some ⟨b, hb⟩ := fun h =>
              hd (n1.mpr ((getElem?_eq_some_fin x i hi _).mp h))
            have hff : finFlat (fun b => if x[i]? = some b then [] else visits k (repW x i b)) b =
                visits k (repW x i ⟨b, hb⟩) := by simp [finFlat, hb, hxb]
            rw [hff, e5]
            simp only [exec_ifz, hd, if_false, exec_seq]
            have hlen3' : st3'.regs (c.lenR (k + 1)) = x.length := by
              rw [pr _ (by simp <;> omega)]; exact hlen3
            have hx3' : WordAt st3' (c.buf (k + 1)) 0 x :=
              hx3.congr (fun j _ => pa _ _ (by simp <;> omega))
            have hi3' : st3'.regs (c.iR (k + 1)) = i := by rw [pr _ (by simp <;> omega)]; exact hi3
            have hb3' : st3'.regs (c.aR (k + 1)) = b := by rw [pr _ (by simp <;> omega)]; exact hb3
            obtain ⟨i1, i2, i3, i4⟩ := c.repC_spec inp B k x st3' i ⟨b, hb⟩ hi hlen3' hx3' hi3' hb3'
              _ hM
            have hInv4 := hstable _ _ _ hInv3'
              (Fr.agree c i3 (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
                (c.ownsArr_of (by simp <;> omega) (by simp <;> omega)))
            obtain ⟨j1, j2, j3⟩ := IH (repW x i ⟨b, hb⟩) acc'' _
              (by rw [repW_length _ _ _ hi]; omega)
              (by
                obtain ⟨T1, hT1⟩ := flatMap_range_split (fun i => (List.range q).flatMap
                  (finFlat fun b => if x[i]? = some b then [] else visits k (repW x i b))) hi
                obtain ⟨T2, hT2⟩ := flatMap_range_split
                  (finFlat fun b => if x[i]? = some b then [] else visits k (repW x i b)) hb
                have hP : acc'' = (Pre ++ ((List.range i).flatMap (fun i => (List.range q).flatMap
                    (finFlat fun b => if x[i]? = some b then [] else visits k (repW x i b)))) ++
                    (List.range b).flatMap
                      (finFlat fun b => if x[i]? = some b then [] else visits k (repW x i b))).foldl
                    f a0 := by
                  rw [hacc'', hacc', hacc]; simp only [List.foldl_append]
                rw [hP]
                refine ok_sub f Ok a0 _ _ _ (T2 ++ T1 ++ Post) ?_ hok
                rw [hV, hT1]
                try simp only at hT2 ⊢
                rw [hT2, hff]
                simp only [List.append_assoc])
              hInv4 i1 i2
            obtain ⟨k35, a35⟩ := c.keep_after_child s (Fr.trans c n3 i3) j2
            refine ⟨by rw [k35 _ (by simp <;> omega) (by simp <;> omega)]; exact hb3, ⟨?_, ?_⟩, ?_⟩
            · refine LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
                (by simp <;> omega)
                (LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
                  (by simp <;> omega) ⟨j1, fun r h1 h2 => ?_, fun y j h1 h2 => ?_⟩ 1) (b + 1)
              · rw [k35 r (by simp at h1 ⊢ <;> omega) h2]; exact hKeep3.1 r h1 h2
              · rw [a35 y j h1 h2]; exact hKeep3.2 y j h1 h2
            · simp only [HS.setR_regs]
              rw [Function.update_of_ne (by simp <;> omega), Function.update_of_ne (by simp <;> omega),
                k35 _ (by simp <;> omega) (by simp <;> omega)]
              exact hi3
            · simp only [cost_seq, cost_ifz]
              rw [← hst3', if_neg hd]
              have := kappa_bits_le B (a := st3'.regs c.d) (M := c.enumM q L s) (by omega)
              have h6 : (7 * x.length + 26) * κ = (7 * x.length + 20) * κ + 6 * κ := by ring
              rw [← hκ] at i4 this
              rw [← hE] at j3
              omega)
      rw [hc''] at R2
      obtain ⟨⟨R2a, R2b⟩, R2c⟩ := R2
      have e6 : (Cmd.seq (lit c.cnt q) (forLoop (c.aR (k + 1)) c.cnt c.one (.seq (c.neqC k)
          (.ifz c.d .skip (.seq (c.repC k) (c.lev q body k)))))).exec inp st' =
          (forLoop (c.aR (k + 1)) c.cnt c.one (.seq (c.neqC k)
          (.ifz c.d .skip (.seq (c.repC k) (c.lev q body k))))).exec inp
            (st'.setR c.cnt q) := rfl
      rw [e6]
      refine ⟨R2b, LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
        (by simp <;> omega)
        (LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
          (by simp <;> omega) R2a 1) (i + 1), ?_⟩
      simp only [cost_seq, cost_lit, exec_lit]
      have K1 := kappa_bits_le B (a := q) (M := c.enumM q L s) (by omega)
      have K2 : 3 * (q + 1) * kappa B (RAM.bits q) ≤ 3 * (q + 1) * κ := Nat.mul_le_mul_left _ K1
      have K3 : q * ((7 * x.length + 26) * κ) + kappa B (RAM.bits q) + 3 * (q + 1) * κ ≤
          (1 + q * (7 * x.length + 26) + 3 * (q + 1)) * κ := by
        have : (1 + q * (7 * x.length + 26) + 3 * (q + 1)) * κ =
          κ + q * ((7 * x.length + 26) * κ) + 3 * (q + 1) * κ := by ring
        omega
      omega)
  rw [hcnt] at R
  obtain ⟨R1, R3⟩ := R
  refine ⟨R1, ?_⟩
  have K1 := kappa_bits_le B (a := x.length) (M := c.enumM q L s) (by simp only [enumM]; omega)
  have K2 : 3 * (x.length + 1) * kappa B (RAM.bits x.length) ≤ 3 * (x.length + 1) * κ :=
    Nat.mul_le_mul_left _ K1
  have K3 : x.length * ((1 + q * (7 * x.length + 26) + 3 * (q + 1)) * κ) +
      3 * (x.length + 1) * κ ≤ 20 * (q + 1) * (x.length + 2) ^ 2 * κ := by
    have : x.length * (1 + q * (7 * x.length + 26) + 3 * (q + 1)) + 3 * (x.length + 1) ≤
        20 * (q + 1) * (x.length + 2) ^ 2 := by
      nlinarith [Nat.zero_le (q * x.length ^ 2), Nat.zero_le (q * x.length), Nat.zero_le (x.length ^ 2)]
    calc _ = (x.length * (1 + q * (7 * x.length + 26) + 3 * (q + 1)) + 3 * (x.length + 1)) * κ := by
          ring
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have hrepLoop : c.repLoop q body k = forLoop (c.iR (k + 1)) c.cnt c.one (.seq (lit c.cnt q)
    (forLoop (c.aR (k + 1)) c.cnt c.one (.seq (c.neqC k)
      (.ifz c.d .skip (.seq (c.repC k) (c.lev q body k)))))) := rfl
  rw [hrepLoop]
  omega

end Phases

end EnumCfg

end EditMulticoloring.Dev.Ram
end

theorem solution.{u_1} : type_of% @EditMulticoloring.Dev.Ram.EnumCfg.repPhase_oai.{u_1} := @EditMulticoloring.Dev.Ram.EnumCfg.repPhase_oai.{u_1}
