-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EnumCfg.delPhase
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:35.65968+00:00
-- url     : https://prove2.me/submissions/e030559c-cb4c-4e24-ab36-7c94157bb0e5

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_delC_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le

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

theorem delW_length {q : ℕ} (x : Word q) (i : ℕ) (hi : i < x.length) :
    (delW x i).length = x.length - 1 := by
  simp [delW]; omega

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

theorem delPhase_oai (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    (k : ℕ) (hk : k + 1 ≤ s) (IH : c.IHk inp B s L body Inv f cb Ok k)
    (x : Word q) (hxL : x.length + (k + 1) ≤ L + s) (a0 : α)
    (hok : ∀ j (hj : j < (visits (k + 1) x).length),
      Ok (((visits (k + 1) x).take j).foldl f a0) ((visits (k + 1) x)[j]))
    (st0 : HS) (hlen0 : st0.regs (c.lenR (k + 1)) = x.length)
    (hx0 : WordAt st0 (c.buf (k + 1)) 0 x) (acc : α) (st : HS)
    (Pre Post : List (Word q))
    (hV : visits (k + 1) x = Pre ++ ((List.range x.length).flatMap (fun i => visits k (delW x i))) ++ Post)
    (hacc : acc = Pre.foldl f a0)
    (hQ : c.LQ Inv s (k + 1) st0 acc st) (hcnt : st.regs c.cnt = x.length) :
    c.LQ Inv s (k + 1) st0
      (((List.range x.length).flatMap (fun i => visits k (delW x i))).foldl f acc)
      ((c.delLoop q body k).exec inp st) ∧
    (c.delLoop q body k).cost inp B st ≤
      ((List.range x.length).flatMap (fun i => visits k (delW x i))).length *
        (cb + c.enumE B q L s) +
      20 * (q + 1) * (x.length + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s)) := by
  set κ := kappa B (RAM.bits (c.enumM q L s)) with hκ
  set E := c.enumE B q L s
  have hM : 2 * c.a0 + 2 * x.length + 2 * k + q + 4 ≤ c.enumM q L s := by
    simp only [enumM]; omega
  have R := forLoop_fold inp B (c.iR (k + 1)) c.cnt c.one (.seq (c.delC k) (c.lev q body k)) st
    (by simp <;> omega) (by simp <;> omega)
    (fun i => visits k (delW x i)) f
    (c.LQ Inv s (k + 1) st0) (cb + E) ((7 * x.length + 20) * κ) acc
    (LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
      (by simp <;> omega) hQ 0)
    (by
      intro i hi acc'' st3 ⟨hInv3, hKeep3⟩ hacc'' hi3
      rw [hcnt] at hi
      have hlen3 : st3.regs (c.lenR (k + 1)) = x.length :=
        (hKeep3.1 _ le_rfl (by simp <;> omega)).trans hlen0
      have hx3 : WordAt st3 (c.buf (k + 1)) 0 x :=
        hx0.congr (fun j _ => hKeep3.2 _ _ le_rfl (by simp <;> omega))
      obtain ⟨i1, i2, i3, i4⟩ := c.delC_spec inp B k x st3 i hi hlen3 hx3 hi3 _ hM
      have hInv4 := hstable _ _ _ hInv3
        (Fr.agree c i3 (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
          (c.ownsArr_of (by simp <;> omega) (by simp <;> omega)))
      obtain ⟨j1, j2, j3⟩ := IH (delW x i) acc'' _
        (by rw [delW_length _ _ hi]; omega)
        (by
          obtain ⟨T1, hT1⟩ := flatMap_range_split (fun i => visits k (delW x i)) hi
          have hP : acc'' = (Pre ++ (List.range i).flatMap (fun i => visits k (delW x i))).foldl f a0 := by
            rw [hacc'', hacc]; simp only [List.foldl_append]
          rw [hP]
          refine ok_sub f Ok a0 _ _ _ (T1 ++ Post) ?_ hok
          rw [hV, hT1]
          simp only [List.append_assoc])
        hInv4 i1 i2
      obtain ⟨k35, a35⟩ := c.keep_after_child s i3 j2
      have e5 : (Cmd.seq (c.delC k) (c.lev q body k)).exec inp st3 =
          (c.lev q body k).exec inp ((c.delC k).exec inp st3) := rfl
      rw [e5]
      refine ⟨by rw [k35 _ (by simp <;> omega) (by simp <;> omega)]; exact hi3, ?_, ?_⟩
      · refine LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
          (by simp <;> omega)
          (LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
            (by simp <;> omega) ⟨j1, fun r h1 h2 => ?_, fun y j h1 h2 => ?_⟩ 1) (i + 1)
        · rw [k35 r (by simp at h1 ⊢ <;> omega) h2]; exact hKeep3.1 r h1 h2
        · rw [a35 y j h1 h2]; exact hKeep3.2 y j h1 h2
      · simp only [cost_seq]
        linarith)
  rw [hcnt] at R
  obtain ⟨R1, R3⟩ := R
  refine ⟨R1, ?_⟩
  have K1 := kappa_bits_le B (a := x.length) (M := c.enumM q L s) (by simp only [enumM]; omega)
  have K2 : 3 * (x.length + 1) * kappa B (RAM.bits x.length) ≤ 3 * (x.length + 1) * κ :=
    Nat.mul_le_mul_left _ K1
  have K3 : x.length * ((7 * x.length + 20) * κ) +
      3 * (x.length + 1) * κ ≤ 20 * (q + 1) * (x.length + 2) ^ 2 * κ := by
    have : x.length * (7 * x.length + 20) + 3 * (x.length + 1) ≤
        20 * (q + 1) * (x.length + 2) ^ 2 := by
      nlinarith [Nat.zero_le (q * x.length ^ 2), Nat.zero_le (q * x.length), Nat.zero_le (x.length ^ 2)]
    calc _ = (x.length * (7 * x.length + 20) + 3 * (x.length + 1)) * κ := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have hdelLoop : c.delLoop q body k =
      forLoop (c.iR (k + 1)) c.cnt c.one (.seq (c.delC k) (c.lev q body k)) := rfl
  rw [hdelLoop]
  omega

end Phases

end EnumCfg

end EditMulticoloring.Dev.Ram
end

theorem solution.{u_1} : type_of% @EditMulticoloring.Dev.Ram.EnumCfg.delPhase_oai.{u_1} := @EditMulticoloring.Dev.Ram.EnumCfg.delPhase_oai.{u_1}
