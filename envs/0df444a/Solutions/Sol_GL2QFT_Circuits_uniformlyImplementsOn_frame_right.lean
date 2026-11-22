-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_frame_right
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:50:41.452027+00:00
-- url     : https://prove2.me/submissions/3c8194d6-4dce-4d60-a004-2268841877c1

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_Turing_TM2ComputableInPolyTime_comp_of_polytime
import Theorems.Thm_QAlgorithms_DeWolf_clocked_tm2_polytime

set_option autoImplicit false

noncomputable section

open Classical
open scoped BigOperators

namespace GL2QFT_FrameRight_Aux

open GL2QFT GL2QFT.Circuits QAlgorithms QAlgorithms.Complexity
open OAI.MetricKMedian.Binary

/-! ### Part 1: PolyTimeComputable combinators (`thread`, `fanout`) -/

private def tStore {K : Type} {Γ : K → Type} (s : ∀ k, List (Γ k)) (xs ys : List Bool) :
    ∀ k : K ⊕ Bool, List (Sum.elim Γ (fun _ => Bool) k)
  | .inl k => s k
  | .inr false => xs
  | .inr true => ys

private lemma tStore_update_inl {K : Type} [DecidableEq K] {Γ : K → Type}
    (s : ∀ k, List (Γ k)) (xs ys : List Bool) (k : K) (w : List (Γ k)) :
    Function.update (tStore s xs ys) (.inl k) w = tStore (Function.update s k w) xs ys := by
  funext j
  rcases j with j | b
  · by_cases h : j = k
    · subst h; simp [Function.update, tStore]
    · simp [Function.update, tStore, h]
  · cases b <;> simp [Function.update, tStore]

private lemma tStore_update_source {K : Type} [DecidableEq K] {Γ : K → Type}
    (s : ∀ k, List (Γ k)) (xs ys w : List Bool) :
    Function.update (tStore s xs ys) (.inr false) w = tStore s w ys := by
  funext j
  rcases j with j | (_ | _) <;> simp [Function.update, tStore]

private lemma tStore_update_buffer {K : Type} [DecidableEq K] {Γ : K → Type}
    (s : ∀ k, List (Γ k)) (xs ys w : List Bool) :
    Function.update (tStore s xs ys) (.inr true) w = tStore s xs w := by
  funext j
  rcases j with j | (_ | _) <;> simp [Function.update, tStore]

private def tEmbedStmt (tm : Turing.FinTM2) :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      Turing.TM2.Stmt (@Sum.elim tm.K Bool Type tm.Γ (fun _ => Bool)) (tm.Λ ⊕ Fin 4)
        (tm.σ × Option Bool)
  | .push k f q => .push (.inl k) (fun v => f v.1) (tEmbedStmt tm q)
  | .peek k f q => .peek (.inl k) (fun v x => (f v.1 x, v.2)) (tEmbedStmt tm q)
  | .pop k f q => .pop (.inl k) (fun v x => (f v.1 x, v.2)) (tEmbedStmt tm q)
  | .load f q => .load (fun v => (f v.1, v.2)) (tEmbedStmt tm q)
  | .branch f q r => .branch (fun v => f v.1) (tEmbedStmt tm q) (tEmbedStmt tm r)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun _ => .inr 2)

private def tEmbedCfg (tm : Turing.FinTM2) (tail : List Bool) (a : tm.Cfg) :
    Turing.TM2.Cfg (@Sum.elim tm.K Bool Type tm.Γ (fun _ => Bool)) (tm.Λ ⊕ Fin 4)
      (tm.σ × Option Bool) :=
  ⟨a.l.elim (some (.inr 2)) (fun l => some (.inl l)), (a.var, none), tStore a.stk tail []⟩

private lemma tStepAux_embed (tm : Turing.FinTM2) (tail : List Bool)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (s : ∀ k, List (tm.Γ k)) :
    let _ := tm.kDecidableEq
    Turing.TM2.stepAux (tEmbedStmt tm q) (v, none) (tStore s tail []) =
      tEmbedCfg tm tail (Turing.TM2.stepAux q v s) := by
  let _ := tm.kDecidableEq
  induction q generalizing v s with
  | push k f q ih =>
      simp only [tEmbedStmt, Turing.TM2.stepAux]
      convert ih v (Function.update s k (f v :: s k)) using 2
      exact tStore_update_inl s tail [] k (f v :: s k)
  | peek k f q ih =>
      simp only [tEmbedStmt, Turing.TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [tEmbedStmt, Turing.TM2.stepAux]
      change Turing.TM2.stepAux (tEmbedStmt tm q) (f v (s k).head?, none)
          (Function.update (tStore s tail []) (.inl k) (s k).tail) = _
      rw [tStore_update_inl]
      exact ih _ _
  | load f q ih =>
      simp only [tEmbedStmt, Turing.TM2.stepAux]
      exact ih _ _
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [tEmbedStmt, Turing.TM2.stepAux, h, Bool.cond_false, Bool.cond_true]
      · exact ihr _ _
      · exact ihq _ _
  | goto f => simp [tEmbedStmt, Turing.TM2.stepAux, tEmbedCfg]
  | halt => simp [tEmbedStmt, Turing.TM2.stepAux, tEmbedCfg]

private def tCode {g : Str → Str}
    (M : Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g) :
    M.tm.Λ ⊕ Fin 4 →
      Turing.TM2.Stmt (@Sum.elim M.tm.K Bool Type M.tm.Γ (fun _ => Bool)) (M.tm.Λ ⊕ Fin 4)
        (M.tm.σ × Option Bool)
  | .inl l => tEmbedStmt M.tm (M.tm.m l)
  | .inr 0 =>
      .pop (.inr false) (fun v b => (v.1, b))
        (.branch (fun v => v.2.getD false)
          (.pop (.inr false) (fun v b => (v.1, b))
            (.push (.inr true) (fun v => v.2.getD false)
              (.load (fun v => (v.1, none)) (.goto (fun _ => .inr 0)))))
          (.load (fun v => (v.1, none)) (.goto (fun _ => .inr 1))))
  | .inr 1 =>
      .pop (.inr true) (fun v b => (v.1, b))
        (.branch (fun v => v.2.isSome)
          (.push (.inl M.tm.k₀) (fun v => M.inputAlphabet.invFun (v.2.getD false))
            (.load (fun v => (v.1, none)) (.goto (fun _ => .inr 1))))
          (.load (fun v => (v.1, none)) (.goto (fun _ => .inl M.tm.main))))
  | .inr 2 =>
      .pop (.inl M.tm.k₁) (fun v x => (v.1, x.map M.outputAlphabet.toFun))
        (.branch (fun v => v.2.isSome)
          (.push (.inr true) (fun _ => true)
            (.push (.inr true) (fun v => v.2.getD false)
              (.load (fun v => (v.1, none)) (.goto (fun _ => .inr 2)))))
          (.push (.inr true) (fun _ => false)
            (.load (fun v => (v.1, none)) (.goto (fun _ => .inr 3)))))
  | .inr 3 =>
      .pop (.inr true) (fun v b => (v.1, b))
        (.branch (fun v => v.2.isSome)
          (.push (.inr false) (fun v => v.2.getD false)
            (.load (fun v => (v.1, none)) (.goto (fun _ => .inr 3))))
          (.load (fun v => (v.1, none)) .halt))

private lemma tRead_run {g : Str → Str}
    (M : Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g)
    (xs tail buf : List Bool) :
    let _ := M.tm.kDecidableEq
    Trace (Turing.TM2.step (tCode M)) (xs.length + 1)
      ⟨some (.inr 0), (M.tm.initialState, none), tStore (fun _ => []) (quote xs ++ tail) buf⟩
      ⟨some (.inr 1), (M.tm.initialState, none), tStore (fun _ => []) tail (xs.reverse ++ buf)⟩ := by
  let _ := M.tm.kDecidableEq
  induction xs generalizing buf with
  | nil =>
      refine Trace.cons ?_ (Trace.refl _)
      simp [Turing.TM2.step, tCode, Turing.TM2.stepAux, quote, tStore, tStore_update_source]
  | cons b xs ih =>
      have hstep :
          Turing.TM2.step (tCode M)
            ⟨some (.inr 0), (M.tm.initialState, none),
              tStore (fun _ => []) (quote (b :: xs) ++ tail) buf⟩ =
          some ⟨some (.inr 0), (M.tm.initialState, none),
              tStore (fun _ => []) (quote xs ++ tail) (b :: buf)⟩ := by
        simp [Turing.TM2.step, tCode, Turing.TM2.stepAux, quote, tStore, tStore_update_source,
          tStore_update_buffer]
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
        Trace.cons hstep (ih (b :: buf))

private lemma tLoad_run {g : Str → Str}
    (M : Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g)
    (tail buf : List Bool) (ys : List (M.tm.Γ M.tm.k₀)) :
    let _ := M.tm.kDecidableEq
    Trace (Turing.TM2.step (tCode M)) (buf.length + 1)
      ⟨some (.inr 1), (M.tm.initialState, none),
        tStore (Function.update (fun _ => []) M.tm.k₀ ys) tail buf⟩
      ⟨some (.inl M.tm.main), (M.tm.initialState, none),
        tStore (Function.update (fun _ => []) M.tm.k₀ (buf.reverse.map M.inputAlphabet.invFun ++ ys)) tail []⟩ := by
  let _ := M.tm.kDecidableEq
  induction buf generalizing ys with
  | nil =>
      refine Trace.cons ?_ (Trace.refl _)
      simp [Turing.TM2.step, tCode, Turing.TM2.stepAux, tStore, tStore_update_buffer]
  | cons b buf ih =>
      have hstep :
          Turing.TM2.step (tCode M)
            ⟨some (.inr 1), (M.tm.initialState, none),
              tStore (Function.update (fun _ => []) M.tm.k₀ ys) tail (b :: buf)⟩ =
          some ⟨some (.inr 1), (M.tm.initialState, none),
              tStore (Function.update (fun _ => []) M.tm.k₀ (M.inputAlphabet.invFun b :: ys)) tail buf⟩ := by
        simp [Turing.TM2.step, tCode, Turing.TM2.stepAux, tStore, tStore_update_buffer,
          tStore_update_inl, Function.update_idem]
      simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using Trace.cons hstep (ih (M.inputAlphabet.invFun b :: ys))

private lemma tBody_trace {g : Str → Str}
    (M : Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g)
    (tail : List Bool) {n : ℕ} {a b : M.tm.Cfg}
    (h : Trace M.tm.step n a b) :
    let _ := M.tm.kDecidableEq
    Trace (Turing.TM2.step (tCode M)) n (tEmbedCfg M.tm tail a) (tEmbedCfg M.tm tail b) := by
  let _ := M.tm.kDecidableEq
  refine h.map (tEmbedCfg M.tm tail) ?_
  intro x y hxy
  rcases x with ⟨lx, vx, sx⟩
  cases lx with
  | none => cases hxy
  | some l =>
      have hy : y = Turing.TM2.stepAux (M.tm.m l) vx sx := (Option.some.inj hxy).symm
      subst hy
      simp only [tEmbedCfg, Option.elim_some, Turing.TM2.step, tCode]
      exact congrArg some (tStepAux_embed M.tm tail (M.tm.m l) vx sx)

private lemma tEmit_run {g : Str → Str}
    (M : Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g)
    (tail : List Bool) (s : ∀ k, List (M.tm.Γ k)) (zs buf : List Bool)
    (hs : s M.tm.k₁ = zs.map M.outputAlphabet.invFun) :
    let _ := M.tm.kDecidableEq
    ∃ s' : ∀ k, List (M.tm.Γ k),
      Trace (Turing.TM2.step (tCode M)) (zs.length + 1)
        ⟨some (.inr 2), (M.tm.initialState, none), tStore s tail buf⟩
        ⟨some (.inr 3), (M.tm.initialState, none), tStore s' tail ((quote zs).reverse ++ buf)⟩ := by
  let _ := M.tm.kDecidableEq
  induction zs generalizing s buf with
  | nil =>
      refine ⟨s, Trace.cons ?_ (Trace.refl _)⟩
      simp only [List.map_nil] at hs
      have hupd : Function.update s M.tm.k₁ [] = s := by
        funext k
        by_cases hk : k = M.tm.k₁
        · subst hk; simp [hs]
        · simp [Function.update, hk]
      simp [Turing.TM2.step, tCode, Turing.TM2.stepAux, quote, tStore, hs,
        tStore_update_buffer, tStore_update_inl, hupd]
  | cons b zs ih =>
      simp only [List.map_cons] at hs
      let s1 := Function.update s M.tm.k₁ (zs.map M.outputAlphabet.invFun)
      have hs1 : s1 M.tm.k₁ = zs.map M.outputAlphabet.invFun := by simp [s1]
      have hstep :
          Turing.TM2.step (tCode M)
            ⟨some (.inr 2), (M.tm.initialState, none), tStore s tail buf⟩ =
          some ⟨some (.inr 2), (M.tm.initialState, none), tStore s1 tail (b :: true :: buf)⟩ := by
        simp [Turing.TM2.step, tCode, Turing.TM2.stepAux, tStore, hs, s1,
          tStore_update_inl, tStore_update_buffer]
      obtain ⟨s', htr⟩ := ih s1 (b :: true :: buf) hs1
      refine ⟨s', ?_⟩
      simpa only [List.length_cons, quote, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.cons_append, List.nil_append] using Trace.cons hstep htr

private lemma tDrain_run {g : Str → Str}
    (M : Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g)
    (s : ∀ k, List (M.tm.Γ k)) (tail buf : List Bool) :
    let _ := M.tm.kDecidableEq
    Trace (Turing.TM2.step (tCode M)) (buf.length + 1)
      ⟨some (.inr 3), (M.tm.initialState, none), tStore s tail buf⟩
      ⟨none, (M.tm.initialState, none), tStore s (buf.reverse ++ tail) []⟩ := by
  let _ := M.tm.kDecidableEq
  induction buf generalizing tail with
  | nil =>
      refine Trace.cons ?_ (Trace.refl _)
      simp [Turing.TM2.step, tCode, Turing.TM2.stepAux, tStore, tStore_update_buffer]
  | cons b buf ih =>
      have hstep :
          Turing.TM2.step (tCode M)
            ⟨some (.inr 3), (M.tm.initialState, none), tStore s tail (b :: buf)⟩ =
          some ⟨some (.inr 3), (M.tm.initialState, none), tStore s (b :: tail) buf⟩ := by
        simp [Turing.TM2.step, tCode, Turing.TM2.stepAux, tStore, tStore_update_buffer,
          tStore_update_source]
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using Trace.cons hstep (ih (b :: tail))

private def pushes1 {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (k₁ : K) :
    Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push k _ q => (if k = k₁ then 1 else 0) + pushes1 k₁ q
  | .peek _ _ q => pushes1 k₁ q
  | .pop _ _ q => pushes1 k₁ q
  | .load _ q => pushes1 k₁ q
  | .branch _ q r => max (pushes1 k₁ q) (pushes1 k₁ r)
  | .goto _ => 0
  | .halt => 0

private lemma stepAux_stk_length {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (k₁ : K) (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (s : ∀ k, List (Γ k)) :
    ((Turing.TM2.stepAux q v s).stk k₁).length ≤ (s k₁).length + pushes1 k₁ q := by
  induction q generalizing v s with
  | push k f q ih =>
      have h := ih v (Function.update s k (f v :: s k))
      by_cases hk : k = k₁
      · subst hk
        simp only [Function.update_self, List.length_cons] at h
        simp only [Turing.TM2.stepAux, pushes1, ↓reduceIte]
        omega
      · simp only [Function.update_of_ne (Ne.symm hk)] at h
        simp only [Turing.TM2.stepAux, pushes1, if_neg hk, zero_add]
        exact h
  | peek _ _ q ih => exact ih _ _
  | pop k f q ih =>
      have h := ih (f v (s k).head?) (Function.update s k (s k).tail)
      by_cases hk : k = k₁
      · subst hk
        simp only [Function.update_self, List.length_tail] at h
        simp only [Turing.TM2.stepAux, pushes1]
        omega
      · simp only [Function.update_of_ne (Ne.symm hk)] at h
        exact h
  | load _ q ih => exact ih _ _
  | branch f q r ihq ihr =>
      cases h : f v
      · simp only [Turing.TM2.stepAux, h, Bool.cond_false, pushes1]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right _ _) _)
      · simp only [Turing.TM2.stepAux, h, Bool.cond_true, pushes1]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto _ => simp [Turing.TM2.stepAux, pushes1]
  | halt => simp [Turing.TM2.stepAux, pushes1]

private lemma trace_stk_length (tm : Turing.FinTM2) :
    letI := tm.kDecidableEq
    letI := tm.ΛFin
    ∀ {n : ℕ} {a b : tm.Cfg}, Trace tm.step n a b →
      (b.stk tm.k₁).length ≤ (a.stk tm.k₁).length + n * (∑ l : tm.Λ, pushes1 tm.k₁ (tm.m l)) := by
  let _ := tm.kDecidableEq
  let _ := tm.ΛFin
  intro n a b htr
  induction htr with
  | refl => simp
  | @cons n a b c hab hbc ih =>
      rcases a with ⟨la, va, sa⟩
      cases la with
      | none => cases hab
      | some l =>
          have hb : b = Turing.TM2.stepAux (tm.m l) va sa := (Option.some.inj hab).symm
          have hstep : (b.stk tm.k₁).length ≤ (sa tm.k₁).length + pushes1 tm.k₁ (tm.m l) := by
            rw [hb]; exact stepAux_stk_length tm.k₁ (tm.m l) va sa
          have hle : pushes1 tm.k₁ (tm.m l) ≤ ∑ l' : tm.Λ, pushes1 tm.k₁ (tm.m l') :=
            Finset.single_le_sum (f := fun l' => pushes1 tm.k₁ (tm.m l'))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
          have hbc' : (c.stk tm.k₁).length ≤
              (b.stk tm.k₁).length + n * ∑ l' : tm.Λ, pushes1 tm.k₁ (tm.m l') := ih
          have h1 : (c.stk tm.k₁).length ≤
              (sa tm.k₁).length + (n + 1) * ∑ l' : tm.Λ, pushes1 tm.k₁ (tm.m l') := by
            rw [Nat.add_mul, one_mul]
            omega
          exact h1

private lemma poly_le_pow (P : Polynomial ℕ) :
    ∃ c d : ℕ, ∀ m : ℕ, P.eval m ≤ (m + c) ^ d := by
  let S : ℕ := 1 + P.sum (fun _ a => a)
  refine ⟨S, P.natDegree + 1, fun m => ?_⟩
  have hsum : P.eval m ≤ P.sum (fun _ a => a) * (m + 1) ^ P.natDegree := by
    rw [Polynomial.eval_eq_sum]
    calc
      P.sum (fun i a => a * m ^ i)
          ≤ P.sum (fun _ a => a * (m + 1) ^ P.natDegree) := by
            refine Finset.sum_le_sum fun i hi => ?_
            refine Nat.mul_le_mul_left _ ?_
            have hdeg : i ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp i hi
            exact (Nat.pow_le_pow_left (Nat.le_succ m) i).trans
              (Nat.pow_le_pow_right (Nat.succ_pos m) hdeg)
      _ = P.sum (fun _ a => a) * (m + 1) ^ P.natDegree := by
            simp only [Polynomial.sum, ← Finset.sum_mul]
  have h1 : P.sum (fun _ a => a) ≤ m + S := by omega
  have h2 : m + 1 ≤ m + S := by omega
  calc
    P.eval m ≤ P.sum (fun _ a => a) * (m + 1) ^ P.natDegree := hsum
    _ ≤ (m + S) * (m + S) ^ P.natDegree :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 P.natDegree)
    _ = (m + S) ^ (P.natDegree + 1) := by rw [pow_succ']

private lemma initList_stk_length (tm : Turing.FinTM2) (s : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm s).stk k).length ≤ s.length := by
  simp only [Turing.initList]
  split_ifs with hk
  · subst hk; simp
  · simp

private lemma thread_polytime {g : Str → Str} (hg : PolyTimeComputable g) :
    ∃ u : Str → Str, PolyTimeComputable u ∧
      ∀ a b : Str, u (quote a ++ b) = quote (g a) ++ b := by
  obtain ⟨M⟩ := hg
  let _ := M.tm.kDecidableEq
  let _ := M.tm.kFin
  let _ := M.tm.ΛFin
  let _ := M.tm.σFin
  let _ : Inhabited (@Sum.elim M.tm.K Bool Type M.tm.Γ (fun _ => Bool) (.inr false)) := ⟨false⟩
  let _ : Fintype (@Sum.elim M.tm.K Bool Type M.tm.Γ (fun _ => Bool) (.inr false)) :=
    inferInstanceAs (Fintype Bool)
  let G : ℕ := ∑ l : M.tm.Λ, pushes1 M.tm.k₁ (M.tm.m l)
  let Q : Polynomial ℕ :=
    5 * Polynomial.X + Polynomial.C (3 * G + 1) * M.time + 5
  obtain ⟨c, d, hQ⟩ := poly_le_pow Q
  have hmain := QAlgorithms.DeWolf.clocked_tm2_polytime
    (K := M.tm.K ⊕ Bool) (Γ := @Sum.elim M.tm.K Bool Type M.tm.Γ (fun _ => Bool))
    (.inr false) (.inr false)
    (tCode M) (.inr 0) c d (M.tm.initialState, none)
    (Equiv.refl Bool) (Equiv.refl Bool)
    (I := Str × Str) (fun p => quote p.1 ++ p.2) (fun p => quote (g p.1) ++ p.2)
    (fun p => by
      rcases p with ⟨xs, tail⟩
      have hm := M.outputsFun xs
      have htr : Trace M.tm.step hm.steps
          (Turing.initList M.tm (xs.map M.inputAlphabet.invFun))
          (Turing.haltList M.tm ((g xs).map M.outputAlphabet.invFun)) :=
        Trace.of_iterate hm.evals_in_steps
      have hstk : ((Turing.haltList M.tm ((g xs).map M.outputAlphabet.invFun)).stk M.tm.k₁).length ≤
          ((Turing.initList M.tm (xs.map M.inputAlphabet.invFun)).stk M.tm.k₁).length +
            hm.steps * G :=
        trace_stk_length M.tm htr
      have hinit_len :
          ((Turing.initList M.tm (xs.map M.inputAlphabet.invFun)).stk M.tm.k₁).length ≤
            xs.length := by
        have h := initList_stk_length M.tm (xs.map M.inputAlphabet.invFun) M.tm.k₁
        simpa using h
      have hhalt_len :
          ((Turing.haltList M.tm ((g xs).map M.outputAlphabet.invFun)).stk M.tm.k₁).length =
            (g xs).length := by
        simp [Turing.haltList]
      have hglen : (g xs).length ≤ xs.length + M.time.eval xs.length * G := by
        have h1 : hm.steps * G ≤ M.time.eval xs.length * G :=
          Nat.mul_le_mul_right G hm.steps_le_m
        omega
      have hread := tRead_run M xs tail []
      simp only [List.append_nil] at hread
      have hload := tLoad_run M tail xs.reverse []
      simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hload
      have hupd_nil : Function.update (fun k : M.tm.K => ([] : List (M.tm.Γ k))) M.tm.k₀ [] =
          fun k : M.tm.K => ([] : List (M.tm.Γ k)) := by
        funext k
        by_cases hk : k = M.tm.k₀
        · subst hk; simp [Function.update]
        · simp [Function.update, hk]
      rw [hupd_nil] at hload
      have hinit_eq :
          (⟨some (.inl M.tm.main), (M.tm.initialState, none),
            tStore (Function.update (fun _ => []) M.tm.k₀ (xs.map M.inputAlphabet.invFun)) tail []⟩ :
            Turing.TM2.Cfg (@Sum.elim M.tm.K Bool Type M.tm.Γ (fun _ => Bool)) (M.tm.Λ ⊕ Fin 4)
              (M.tm.σ × Option Bool)) =
          tEmbedCfg M.tm tail (Turing.initList M.tm (xs.map M.inputAlphabet.invFun)) := by
        simp only [tEmbedCfg, Turing.initList, Option.elim_some]
        congr 1
        funext k
        rcases k with k | (_ | _)
        · simp only [tStore, Function.update]
          by_cases hk : k = M.tm.k₀
          · subst hk; simp
          · simp [hk]
        · rfl
        · rfl
      rw [hinit_eq] at hload
      have hbody := tBody_trace M tail htr
      have hhalt_eq :
          tEmbedCfg M.tm tail (Turing.haltList M.tm ((g xs).map M.outputAlphabet.invFun)) =
          ⟨some (.inr 2), (M.tm.initialState, none),
            tStore (Turing.haltList M.tm ((g xs).map M.outputAlphabet.invFun)).stk tail []⟩ := rfl
      rw [hhalt_eq] at hbody
      obtain ⟨s', hemit⟩ := tEmit_run M tail
        (Turing.haltList M.tm ((g xs).map M.outputAlphabet.invFun)).stk (g xs) []
        (by simp [Turing.haltList])
      simp only [List.append_nil] at hemit
      have hdrain := tDrain_run M s' tail (quote (g xs)).reverse
      simp only [List.length_reverse, quote_length, List.reverse_reverse] at hdrain
      have hfull := (((hread.trans hload).trans hbody).trans hemit).trans hdrain
      let N := xs.length + 1 + (xs.length + 1) + hm.steps + ((g xs).length + 1) +
          (2 * (g xs).length + 1 + 1)
      have hN_pos : 1 ≤ N := by dsimp [N]; omega
      refine ⟨N - 1, ?_,
        ⟨⟨none, (M.tm.initialState, none), tStore s' (quote (g xs) ++ tail) []⟩, ?_, rfl, ?_⟩⟩
      · have hmlen : xs.length ≤ (quote xs ++ tail).length := by
          simp only [List.length_append, quote_length]; omega
        have htime_mono : M.time.eval xs.length ≤ M.time.eval (quote xs ++ tail).length :=
          polynomial_eval_mono M.time hmlen
        have hN_le : N ≤ Q.eval (quote xs ++ tail).length := by
          simp only [N, Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_ofNat]
          have hsteps := hm.steps_le_m.trans htime_mono
          have hg2 : (g xs).length ≤ (quote xs ++ tail).length + M.time.eval (quote xs ++ tail).length * G :=
            hglen.trans (Nat.add_le_add hmlen (Nat.mul_le_mul_right G htime_mono))
          nlinarith
        exact (Nat.sub_le N 1).trans (hN_le.trans (hQ _))
      · rw [Nat.sub_add_cancel hN_pos]
        dsimp only
        convert hfull.iterate_eq using 3
        congr 1
        funext k
        rcases k with k | (_ | _)
        · simp [Function.update, tStore]
        · simp only [Function.update, tStore, ↓reduceDIte]
          change List.map (⇑(Equiv.refl Bool).symm) (quote xs ++ tail) = quote xs ++ tail
          induction (quote xs ++ tail) with
          | nil => rfl
          | cons b l ih => exact congrArg (b :: ·) ih
        · simp [Function.update, tStore]
      · dsimp only
        change tStore s' (quote (g xs) ++ tail) [] (.inr false) =
          List.map (⇑(Equiv.refl Bool).symm) (quote (g xs) ++ tail)
        have hmap_refl : ∀ l : List Bool,
            l = List.map (⇑(Equiv.refl Bool).symm) l := fun l => by
          induction l with
          | nil => rfl
          | cons b l ih => exact congrArg (b :: ·) ih
        exact hmap_refl (quote (g xs) ++ tail))
  obtain ⟨u, hu, hu_eq⟩ := hmain
  exact ⟨u, hu, fun a b => hu_eq (a, b)⟩

private lemma tm2_thread {g : Str → Str}
    (hg : Nonempty (Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g)) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (encodePair (id : Str → Str) (id : Str → Str))
      (encodePair (id : Str → Str) (id : Str → Str))
      (fun p : Str × Str => (g p.1, p.2))) := by
  obtain ⟨u, ⟨mu⟩, hu_eq⟩ := thread_polytime hg
  exact ⟨{
    tm := mu.tm
    inputAlphabet := mu.inputAlphabet
    outputAlphabet := mu.outputAlphabet
    time := mu.time
    outputsFun := fun p => by
      have h := mu.outputsFun (encodePair id id p)
      simpa only [id_eq, encodePair, hu_eq p.1 p.2] using h
  }⟩

private lemma polyTimeComputable_fanout {g₁ g₂ : Str → Str}
    (h₁ : PolyTimeComputable g₁) (h₂ : PolyTimeComputable g₂) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (id : Str → Str) (encodePair (id : Str → Str) (id : Str → Str))
      (fun x : Str => (g₁ x, g₂ x))) := by
  obtain ⟨m1⟩ := tm2_thread h₁
  obtain ⟨m2⟩ := tm2_thread h₂
  obtain ⟨mc1⟩ := Turing.TM2ComputableInPolyTime.comp_of_polytime
    (PolyProgram.duplicate id).stock m1
  obtain ⟨mc2⟩ := Turing.TM2ComputableInPolyTime.comp_of_polytime
    mc1 (PolyProgram.exchange id id).stock
  obtain ⟨mc3⟩ := Turing.TM2ComputableInPolyTime.comp_of_polytime mc2 m2
  obtain ⟨mc4⟩ := Turing.TM2ComputableInPolyTime.comp_of_polytime
    mc3 (PolyProgram.exchange id id).stock
  exact ⟨{
    tm := mc4.tm
    inputAlphabet := mc4.inputAlphabet
    outputAlphabet := mc4.outputAlphabet
    time := mc4.time
    outputsFun := fun x => by
      have h := mc4.outputsFun x
      simpa [Function.comp_apply, Prod.swap] using h
  }⟩

/-! ### Part 2: Pure PolyPrograms for extracting `D.encData`, extracting `ones`, and right-shifting `encLayer` -/

private def dropTrueT : Transducer where
  Q := Bool
  initial := false
  next q b := (q || !b, if q || !b then [b] else [])
  finish _ := []

private lemma dropTrueT_true (xs : List Bool) : dropTrueT.run true xs = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [b] ++ dropTrueT.run true xs = b :: xs
      rw [ih]; rfl

private lemma dropTrueT_run (xs : List Bool) : dropTrueT.run false xs = xs.dropWhile id := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · change [false] ++ dropTrueT.run true xs = (false :: xs).dropWhile id
        rw [dropTrueT_true]
        simp
      · change [] ++ dropTrueT.run false xs = (true :: xs).dropWhile id
        rw [ih]
        simp

private def extractData (xs : Str) : Str :=
  (xs.reverse.tail.dropWhile id).reverse

private noncomputable def extractDataProgram : PolyProgram id id extractData :=
  let dp : PolyProgram id id (List.dropWhile id) :=
    dropTrueT.program.of_word (eb := id) (f := List.dropWhile id) dropTrueT_run
  ((PolyProgram.reverse.comp PolyProgram.tail).comp dp).comp PolyProgram.reverse

private lemma encBin_getLast (m : ℕ) : ∃ p, LocalHamiltonian.encBin m = p ++ [false] := by
  refine ⟨(Nat.bits m).flatMap (fun β => [true, β]) ++ [false], ?_⟩
  simp [LocalHamiltonian.encBin, List.append_assoc]

private lemma dropWhile_replicate_true (k : ℕ) (ys : List Bool) :
    (List.replicate k true ++ false :: ys).dropWhile id = false :: ys := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

private lemma encData_ends_false (D : FieldData) : ∃ p, D.encData = p ++ [false] := by
  obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero D.hr.ne'
  let f := fun j => (List.range D.r).flatMap fun l =>
    LocalHamiltonian.encBin (D.digit ((AdjoinRoot.modByMonicHom D.F_monic D.h).coeff j) l)
  have hrange2 : List.range 2 = [0, 1] := by decide
  have hrangeR : List.range D.r = List.range r' ++ [r'] := by
    rw [hr', List.range_succ]
  obtain ⟨p0, hp0⟩ := encBin_getLast (D.digit ((AdjoinRoot.modByMonicHom D.F_monic D.h).coeff 1) r')
  have hlast : f 1 = ((List.range r').flatMap fun l =>
      LocalHamiltonian.encBin (D.digit ((AdjoinRoot.modByMonicHom D.F_monic D.h).coeff 1) l)) ++ p0 ++ [false] := by
    dsimp [f]
    rw [hrangeR, List.flatMap_append, List.flatMap_singleton, hp0, List.append_assoc]
  refine ⟨LocalHamiltonian.encBin D.p ++ LocalHamiltonian.encBin D.r ++
      ((List.range (D.r + 1)).flatMap fun j => LocalHamiltonian.encBin (D.f.coeff j).val) ++
      ((List.range 3).flatMap fun j =>
        (List.range D.r).flatMap fun l => LocalHamiltonian.encBin (D.digit (D.F.coeff j) l)) ++
      f 0 ++ ((List.range r').flatMap fun l =>
        LocalHamiltonian.encBin (D.digit ((AdjoinRoot.modByMonicHom D.F_monic D.h).coeff 1) l)) ++ p0, ?_⟩
  change LocalHamiltonian.encBin D.p ++ LocalHamiltonian.encBin D.r ++
      ((List.range (D.r + 1)).flatMap fun j => LocalHamiltonian.encBin (D.f.coeff j).val) ++
      ((List.range 3).flatMap fun j =>
        (List.range D.r).flatMap fun l => LocalHamiltonian.encBin (D.digit (D.F.coeff j) l)) ++
      ((List.range 2).flatMap f) = _
  rw [hrange2, List.flatMap_cons, List.flatMap_singleton, hlast]
  simp only [List.append_assoc]

private lemma extractData_encData (D : FieldData) (k : ℕ) :
    extractData (D.encData ++ encNat k) = D.encData := by
  obtain ⟨p, hp⟩ := encData_ends_false D
  rw [hp]
  simp only [extractData, encNat, List.append_assoc, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.reverse_replicate, List.cons_append, List.tail_cons]
  rw [dropWhile_replicate_true k p.reverse]
  simp

private def takeWhileTrueT : Transducer where
  Q := Bool
  initial := true
  next q b := (q && b, if q && b then [true] else [])
  finish _ := []

private lemma takeWhileTrueT_false (xs : List Bool) : takeWhileTrueT.run false xs = [] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [] ++ takeWhileTrueT.run false xs = []
      rw [ih]; rfl

private lemma takeWhileTrueT_run (xs : List Bool) :
    takeWhileTrueT.run true xs = xs.takeWhile id := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · change [] ++ takeWhileTrueT.run false xs = (false :: xs).takeWhile id
        rw [takeWhileTrueT_false]
        simp
      · change [true] ++ takeWhileTrueT.run true xs = (true :: xs).takeWhile id
        rw [ih]
        simp

private lemma takeWhile_encNat (n : ℕ) :
    (encNat n).takeWhile id = List.replicate n true := by
  induction n with
  | zero => simp [encNat]
  | succ n _ => simp [encNat, List.replicate_succ]

private def toEncodedBoolListT : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((), [true, b, false])
  finish _ := []

private lemma toEncodedBoolListT_run (xs : List Bool) :
    toEncodedBoolListT.run () xs = encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [true, b, false] ++ toEncodedBoolListT.run () xs = quote (encodeBool b) ++ encodeList encodeBool xs
      rw [ih]
      simp [encodeBool, quote]

private def encFin12 (p : Fin 12) : List Bool := List.replicate p.val true ++ [false]

private lemma encFin12_injective : Function.Injective encFin12 := by
  intro a b h
  have hl := congrArg List.length h
  simp only [encFin12, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at hl
  exact Fin.ext (by omega)

private lemma encFin12_length (p : Fin 12) : (encFin12 p).length ≤ 12 := by
  simp only [encFin12, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

private def rightNext (x : Fin 12 × (Bool × Bool)) : Fin 12 :=
  match x.1.val, x.2.1, x.2.2 with
  | 0, _, true => 1
  | 0, _, false => 2
  | 1, _, true => 1
  | 1, _, false => 2
  | 2, _, true => 2
  | 2, _, false => 3
  | 3, _, true => 4
  | 3, _, false => 8
  | 4, _, true => 5
  | 4, _, false => 8
  | 5, _, true => 6
  | 5, _, false => 8
  | 6, _, true => 7
  | 6, _, false => 8
  | 7, _, true => 7
  | 7, _, false => 10
  | 8, _, false => 3
  | 8, false, true => 8
  | 8, true, true => 9
  | 9, _, true => 9
  | 9, _, false => 3
  | 10, _, false => 8
  | 10, false, true => 10
  | 10, true, true => 11
  | 11, _, true => 11
  | 11, _, false => 8
  | _, _, _ => 0

private def rightShiftNow (x : Fin 12 × Bool) : Bool :=
  x.1 == 0 || ((x.1 == 8 || x.1 == 10) && x.2)

private def rightResetW (x : Fin 12 × Bool) : Bool :=
  !x.2 && (x.1 == 8 || x.1 == 9 || x.1 == 10 || x.1 == 11)

private def rightPopW (x : Fin 12 × (Bool × Bool)) : Bool :=
  (x.1 == 8 || x.1 == 10) && !x.2.1 && x.2.2

private abbrev RightAcc := Fin 12 × (List Bool × (List Bool × (List Bool × List Bool)))

private abbrev ebRight : RightAcc → List Bool :=
  encodePair encFin12
    (encodePair (id : Str → Str)
      (encodePair (id : Str → Str) (encodePair (id : Str → Str) (id : Str → Str))))

private def rightStep (x : RightAcc × Bool) : RightAcc :=
  let s := x.1
  let b := x.2
  let p := s.1
  let onesW := s.2.1
  let wRem := s.2.2.1
  let onesB := s.2.2.2.1
  let revOut := s.2.2.2.2
  let e := wRem.isEmpty
  let p' := rightNext (p, (e, b))
  let wRem' := if rightResetW (p, b) then onesW else if rightPopW (p, (e, b)) then wRem.tail else wRem
  let revOut' := b :: (if rightShiftNow (p, e) then onesB ++ revOut else revOut)
  (p', (onesW, (wRem', (onesB, revOut'))))

private noncomputable def rightStepProgram :
    PolyProgram (encodePair ebRight encodeBool) ebRight rightStep := by
  let ps := PolyProgram.fst ebRight encodeBool
  let pb := PolyProgram.snd ebRight encodeBool
  let eTail := encodePair (id : Str → Str)
    (encodePair (id : Str → Str) (encodePair (id : Str → Str) (id : Str → Str)))
  let pp := ps.comp (PolyProgram.fst encFin12 eTail)
  let pTail := ps.comp (PolyProgram.snd encFin12 eTail)
  let eBR := encodePair (id : Str → Str) (id : Str → Str)
  let eWBR := encodePair (id : Str → Str) eBR
  let ponesW := pTail.comp (PolyProgram.fst (id : Str → Str) eWBR)
  let pWBR := pTail.comp (PolyProgram.snd (id : Str → Str) eWBR)
  let pwRem := pWBR.comp (PolyProgram.fst (id : Str → Str) eBR)
  let pBR := pWBR.comp (PolyProgram.snd (id : Str → Str) eBR)
  let ponesB := pBR.comp (PolyProgram.fst (id : Str → Str) (id : Str → Str))
  let prevOut := pBR.comp (PolyProgram.snd (id : Str → Str) (id : Str → Str))
  let pe := pwRem.comp PolyProgram.isEmpty
  let ppeb := pp.fanout (pe.fanout pb)
  let ppe := pp.fanout pe
  let ppb := pp.fanout pb
  let e12b := encodePair encFin12 encodeBool
  let e12bb := encodePair encFin12 (encodePair encodeBool encodeBool)
  have hinj1 : Function.Injective e12b := encodePair_injective encFin12_injective encodeBool_injective
  have hinj2 : Function.Injective e12bb :=
    encodePair_injective encFin12_injective
      (encodePair_injective encodeBool_injective encodeBool_injective)
  let nextP := ppeb.comp (PolyProgram.boolFunction e12bb encFin12 rightNext hinj2)
  let needS := ppe.comp (PolyProgram.boolFunction e12b encodeBool rightShiftNow hinj1)
  let needR := ppb.comp (PolyProgram.boolFunction e12b encodeBool rightResetW hinj1)
  let needPop := ppeb.comp (PolyProgram.boolFunction e12bb encodeBool rightPopW hinj2)
  let poppedOrKeep := PolyProgram.ite needPop pwRem (pwRem.comp PolyProgram.tail)
  let newWRem := PolyProgram.ite needR poppedOrKeep ponesW
  let appOut := (ponesB.fanout prevOut).comp PolyProgram.append
  let emitTail := PolyProgram.ite needS prevOut appOut
  let newOut := (pb.fanout emitTail).comp PolyProgram.cons
  exact (nextP.fanout (ponesW.fanout (newWRem.fanout (ponesB.fanout newOut)))).congr _
    (fun _ => rfl)

private lemma rightStep_bound (pre : List Bool) (s : RightAcc) :
    (pre.foldl (fun b a => rightStep (b, a)) s).2.1 = s.2.1 ∧
    (pre.foldl (fun b a => rightStep (b, a)) s).2.2.1.length ≤
      max s.2.1.length s.2.2.1.length ∧
    (pre.foldl (fun b a => rightStep (b, a)) s).2.2.2.1 = s.2.2.2.1 ∧
    (pre.foldl (fun b a => rightStep (b, a)) s).2.2.2.2.length ≤
      s.2.2.2.2.length + pre.length * (1 + s.2.2.2.1.length) := by
  induction pre generalizing s with
  | nil => simp
  | cons b pre ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih (rightStep (s, b))
      refine ⟨h1, ?_, h3, ?_⟩
      · simp only [List.foldl_cons]
        have hw : (rightStep (s, b)).2.2.1.length ≤ max s.2.1.length s.2.2.1.length := by
          simp only [rightStep]
          split_ifs
          · exact le_max_left _ _
          · simp only [List.length_tail]; exact le_trans (Nat.sub_le _ _) (le_max_right _ _)
          · exact le_max_right _ _
        have h1' : (rightStep (s, b)).2.1 = s.2.1 := rfl
        rw [h1'] at h2
        exact le_trans h2 (max_le (le_max_left _ _) hw)
      · simp only [List.foldl_cons, List.length_cons]
        have ho : (rightStep (s, b)).2.2.2.2.length ≤
            s.2.2.2.2.length + (1 + s.2.2.2.1.length) := by
          simp only [rightStep, List.length_cons]
          split_ifs <;> simp <;> omega
        have h3' : (rightStep (s, b)).2.2.2.1 = s.2.2.2.1 := rfl
        rw [h3'] at h4
        nlinarith

private noncomputable def shiftRightFold :
    PolyProgram (encodePair (encodeList encodeBool) ebRight) ebRight
      (fun x => x.1.foldl (fun b a => rightStep (b, a)) x.2) :=
  PolyProgram.listFold rightStepProgram false (Polynomial.X ^ 2 + 3 * Polynomial.X + 40)
    (fun as s pre suf he => by
      obtain ⟨h1, h2, h3, h4⟩ := rightStep_bound pre s
      have h2' : (pre.foldl (fun b a => rightStep (b, a)) s).2.2.1.length ≤
          s.2.1.length + s.2.2.1.length :=
        le_trans h2 (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
      have hpre : pre.length ≤ as.length := by rw [he, List.length_append]; omega
      have has : as.length ≤ (encodeList encodeBool as).length := EncodedList.length_le encodeBool as
      have hf : (encFin12 (pre.foldl (fun b a => rightStep (b, a)) s).1).length ≤ 12 :=
        encFin12_length _
      set L := (encodePair (encodeList encodeBool) ebRight (as, s)).length
      have hL1 : (encodeList encodeBool as).length ≤ L := by
        dsimp [L]; simp [encodePair_length]; omega
      have hL2 : 2 * s.2.1.length + 2 * s.2.2.1.length + 2 * s.2.2.2.1.length +
          s.2.2.2.2.length ≤ L := by
        dsimp [L]; simp [ebRight, encodePair_length]; omega
      simp only [ebRight, encodePair_length, id_eq] at hf ⊢
      rw [h1, h3]
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_ofNat]
      nlinarith)

private def shiftRightFun (p : Str × (Str × Str)) : Str :=
  let onesW := p.1.takeWhile id
  let onesB := p.2.1.takeWhile id
  let acc := p.2.2.foldl (fun b a => rightStep (b, a))
    ((0 : Fin 12), (onesW, (onesW, (onesB, []))))
  acc.2.2.2.2.reverse

private noncomputable def shiftRightProgram :
    PolyProgram
      (encodePair (id : Str → Str) (encodePair (id : Str → Str) (id : Str → Str)))
      id shiftRightFun := by
  let e2 := encodePair (id : Str → Str) (id : Str → Str)
  let ex := encodePair (id : Str → Str) e2
  let pw := PolyProgram.fst (id : Str → Str) e2
  let p2 := PolyProgram.snd (id : Str → Str) e2
  let pb := p2.comp (PolyProgram.fst (id : Str → Str) (id : Str → Str))
  let ps := p2.comp (PolyProgram.snd (id : Str → Str) (id : Str → Str))
  let tw := takeWhileTrueT.program.of_word (eb := id) (f := List.takeWhile id) takeWhileTrueT_run
  let onesW := pw.comp tw
  let onesB := pb.comp tw
  let encS := ps.comp (toEncodedBoolListT.program.of_word (eb := encodeList encodeBool) (f := id)
    toEncodedBoolListT_run)
  let init := (PolyProgram.constant ex encFin12 (0 : Fin 12)).fanout
    (onesW.fanout (onesW.fanout (onesB.fanout (PolyProgram.constant ex (id : Str → Str) []))))
  let fld := (encS.fanout init).comp shiftRightFold
  let eTail := encodePair (id : Str → Str)
    (encodePair (id : Str → Str) (encodePair (id : Str → Str) (id : Str → Str)))
  let getOut := fld.comp
    ((PolyProgram.snd encFin12 eTail).comp
      ((PolyProgram.snd (id : Str → Str) _).comp
        ((PolyProgram.snd (id : Str → Str) _).comp
          (PolyProgram.snd (id : Str → Str) (id : Str → Str)))))
  exact (getOut.comp PolyProgram.reverse).congr _ (fun _ => rfl)

private lemma replicate_true_append_cons (m : ℕ) (r : List Bool) :
    List.replicate m true ++ true :: r = true :: (List.replicate m true ++ r) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, ih]

private lemma replicate_true_assoc_eq (a b : ℕ) (r : List Bool) :
    List.replicate a true ++ true :: (List.replicate b true ++ r) =
      List.replicate b true ++ true :: (List.replicate a true ++ r) := by
  have hL : ∀ x y : ℕ,
      List.replicate x true ++ true :: (List.replicate y true ++ r) =
        List.replicate (x + 1 + y) true ++ r := fun x y => by
    rw [List.replicate_add, List.replicate_add, List.replicate_succ]
    simp [List.append_assoc]
  rw [hL a b, hL b a, show a + 1 + b = b + 1 + a by omega]

private lemma right_foldl_shift_encNat (w bW n : ℕ) (p0 p1 pDone : Fin 12)
    (h0t : ∀ e, rightNext (p0, (e, true)) = p1)
    (h0f : ∀ e, rightNext (p0, (e, false)) = pDone)
    (h1t : ∀ e, rightNext (p1, (e, true)) = p1)
    (h1f : ∀ e, rightNext (p1, (e, false)) = pDone)
    (hs0 : ∀ e, rightShiftNow (p0, e) = true)
    (hs1 : ∀ e, rightShiftNow (p1, e) = false)
    (hr0 : ∀ b, rightResetW (p0, b) = false)
    (hr1 : ∀ b, rightResetW (p1, b) = false)
    (hp0 : ∀ e b, rightPopW (p0, (e, b)) = false)
    (hp1 : ∀ e b, rightPopW (p1, (e, b)) = false)
    (revOut : List Bool) :
    (encNat n).foldl (fun b a => rightStep (b, a))
        (p0, (List.replicate w true, (List.replicate w true, (List.replicate bW true, revOut)))) =
      (pDone, (List.replicate w true, (List.replicate w true, (List.replicate bW true,
        (encNat (n + bW)).reverse ++ revOut)))) := by
  have htail : ∀ (m : ℕ) (r : List Bool),
      (List.replicate m true ++ [false]).foldl (fun b a => rightStep (b, a))
        (p1, (List.replicate w true, (List.replicate w true, (List.replicate bW true, r)))) =
        (pDone, (List.replicate w true, (List.replicate w true, (List.replicate bW true,
          false :: (List.replicate m true ++ r))))) := by
    intro m r
    induction m generalizing r with
    | zero => simp [rightStep, h1f, hs1, hr1, hp1]
    | succ m ih =>
        rw [List.replicate_succ, List.cons_append, List.foldl_cons]
        have hstep : rightStep ((p1, (List.replicate w true, (List.replicate w true,
            (List.replicate bW true, r)))), true) =
            (p1, (List.replicate w true, (List.replicate w true,
              (List.replicate bW true, true :: r)))) := by
          simp [rightStep, h1t, hs1, hr1, hp1]
        rw [hstep, ih (true :: r), replicate_true_append_cons]
        rfl
  cases n with
  | zero =>
      simp [encNat, rightStep, h0f, hs0, hr0, hp0]
  | succ n =>
      rw [encNat, List.replicate_succ, List.cons_append, List.foldl_cons]
      have hfirst : rightStep ((p0, (List.replicate w true, (List.replicate w true,
          (List.replicate bW true, revOut)))), true) =
          (p1, (List.replicate w true, (List.replicate w true,
            (List.replicate bW true, true :: (List.replicate bW true ++ revOut))))) := by
        simp [rightStep, h0t, hs0, hr0, hp0]
      rw [hfirst, htail n]
      have hrep : List.replicate (n + 1 + bW) true =
          List.replicate bW true ++ true :: List.replicate n true := by
        rw [show n + 1 + bW = bW + (n + 1) by omega, List.replicate_add, List.replicate_succ,
          replicate_true_append_cons]
      simp only [encNat, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.reverse_replicate, List.cons_append, Prod.mk.injEq, true_and]
      rw [hrep, List.append_assoc]
      exact congrArg (false :: ·) (replicate_true_assoc_eq n bW revOut)

private lemma right_foldl_copy_encNat (w bW n : ℕ) (p0 pDone : Fin 12)
    (ht : ∀ e, rightNext (p0, (e, true)) = p0)
    (hf : ∀ e, rightNext (p0, (e, false)) = pDone)
    (hs : ∀ e, rightShiftNow (p0, e) = false)
    (hr : ∀ b, rightResetW (p0, b) = false)
    (hp : ∀ e b, rightPopW (p0, (e, b)) = false)
    (revOut : List Bool) :
    (encNat n).foldl (fun b a => rightStep (b, a))
        (p0, (List.replicate w true, (List.replicate w true, (List.replicate bW true, revOut)))) =
      (pDone, (List.replicate w true, (List.replicate w true, (List.replicate bW true,
        (encNat n).reverse ++ revOut)))) := by
  have haux : ∀ (m : ℕ) (r : List Bool),
      (List.replicate m true ++ [false]).foldl (fun b a => rightStep (b, a))
        (p0, (List.replicate w true, (List.replicate w true, (List.replicate bW true, r)))) =
        (pDone, (List.replicate w true, (List.replicate w true, (List.replicate bW true,
          false :: (List.replicate m true ++ r))))) := by
    intro m r
    induction m generalizing r with
    | zero => simp [rightStep, hf, hs, hr, hp]
    | succ m ih =>
        rw [List.replicate_succ, List.cons_append, List.foldl_cons]
        have hstep : rightStep ((p0, (List.replicate w true, (List.replicate w true,
            (List.replicate bW true, r)))), true) =
            (p0, (List.replicate w true, (List.replicate w true,
              (List.replicate bW true, true :: r)))) := by
          simp [rightStep, ht, hs, hr, hp]
        rw [hstep, ih (true :: r), replicate_true_append_cons]
        rfl
  simpa [encNat] using haux n revOut

private lemma right_foldl_compare (w bW : ℕ) (p0 pCopy pDone : Fin 12)
    (h0f : ∀ e, rightNext (p0, (e, false)) = pDone)
    (h0ft : rightNext (p0, (false, true)) = p0)
    (h0tt : rightNext (p0, (true, true)) = pCopy)
    (hct : ∀ e, rightNext (pCopy, (e, true)) = pCopy)
    (hcf : ∀ e, rightNext (pCopy, (e, false)) = pDone)
    (hs0 : ∀ e, rightShiftNow (p0, e) = e)
    (hsc : ∀ e, rightShiftNow (pCopy, e) = false)
    (hr0 : rightResetW (p0, false) = true) (hr0t : rightResetW (p0, true) = false)
    (hrc : rightResetW (pCopy, false) = true) (hrct : rightResetW (pCopy, true) = false)
    (hp0 : ∀ e, rightPopW (p0, (e, true)) = !e)
    (hpc : ∀ e b, rightPopW (pCopy, (e, b)) = false)
    (m k : ℕ) (revOut : List Bool) :
    (encNat m).foldl (fun b a => rightStep (b, a))
        (p0, (List.replicate w true, (List.replicate k true, (List.replicate bW true, revOut)))) =
      (pDone, (List.replicate w true, (List.replicate w true, (List.replicate bW true,
        (encNat (if k ≤ m then m + bW else m)).reverse ++ revOut)))) := by
  have hcopy : ∀ (d : ℕ) (r : List Bool),
      (List.replicate d true ++ [false]).foldl (fun b a => rightStep (b, a))
        (pCopy, (List.replicate w true, ([], (List.replicate bW true, r)))) =
        (pDone, (List.replicate w true, (List.replicate w true, (List.replicate bW true,
          false :: (List.replicate d true ++ r))))) := by
    intro d r
    induction d generalizing r with
    | zero => simp [rightStep, hcf, hsc, hrc]
    | succ d ih =>
        rw [List.replicate_succ, List.cons_append, List.foldl_cons]
        have hstep : rightStep ((pCopy, (List.replicate w true, ([], (List.replicate bW true, r)))), true) =
            (pCopy, (List.replicate w true, ([], (List.replicate bW true, true :: r)))) := by
          simp [rightStep, hct, hsc, hrct, hpc]
        rw [hstep, ih (true :: r), replicate_true_append_cons]
        rfl
  induction k generalizing m revOut with
  | zero =>
      simp only [Nat.zero_le, ↓reduceIte, List.replicate_zero]
      cases m with
      | zero =>
          simp [encNat, rightStep, h0f, hs0, hr0]
      | succ m =>
          rw [encNat, List.replicate_succ, List.cons_append, List.foldl_cons]
          have hfirst : rightStep ((p0, (List.replicate w true, ([], (List.replicate bW true, revOut)))), true) =
              (pCopy, (List.replicate w true, ([], (List.replicate bW true, true :: (List.replicate bW true ++ revOut))))) := by
            simp [rightStep, h0tt, hs0, hr0t, hp0]
          rw [hfirst, hcopy m]
          have hrep : List.replicate (m + 1 + bW) true =
              List.replicate bW true ++ true :: List.replicate m true := by
            rw [show m + 1 + bW = bW + (m + 1) by omega, List.replicate_add, List.replicate_succ,
              replicate_true_append_cons]
          simp only [encNat, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.reverse_replicate, List.cons_append, Prod.mk.injEq, true_and]
          rw [hrep, List.append_assoc]
          exact congrArg (false :: ·) (replicate_true_assoc_eq m bW revOut)
  | succ k ih =>
      cases m with
      | zero =>
          simp [encNat, rightStep, h0f, hs0, hr0, show ¬ (k + 1 ≤ 0) by omega]
      | succ m =>
          change (true :: List.replicate m true ++ [false]).foldl (fun b a => rightStep (b, a))
              (p0, (List.replicate w true, (true :: List.replicate k true, (List.replicate bW true, revOut)))) = _
          rw [List.cons_append, List.foldl_cons]
          have hfirst : rightStep ((p0, (List.replicate w true,
              (true :: List.replicate k true, (List.replicate bW true, revOut)))), true) =
              (p0, (List.replicate w true, (List.replicate k true,
                (List.replicate bW true, true :: revOut)))) := by
            simp [rightStep, h0ft, hs0, hr0t, hp0]
          rw [hfirst]
          have ih' := ih m (true :: revOut)
          change List.foldl (fun b a => rightStep (b, a))
              (p0, (List.replicate w true, (List.replicate k true, (List.replicate bW true, true :: revOut))))
              (encNat m) = _
          rw [ih']
          by_cases hkm : k ≤ m
          · have hkm' : k + 1 ≤ m + 1 := by omega
            simp only [hkm, hkm', ↓reduceIte, encNat, List.reverse_append, List.reverse_cons,
              List.reverse_nil, List.nil_append, List.reverse_replicate, List.cons_append,
              Prod.mk.injEq, true_and]
            rw [show m + 1 + bW = (m + bW) + 1 by omega, List.replicate_succ,
              List.cons_append, replicate_true_append_cons]
          · have hkm' : ¬ (k + 1 ≤ m + 1) := by omega
            simp only [hkm, hkm', ↓reduceIte, encNat, List.reverse_append,
              List.reverse_cons, List.reverse_nil, List.nil_append, List.reverse_replicate,
              List.cons_append, Prod.mk.injEq, true_and]
            rw [replicate_true_append_cons, List.replicate_succ, List.cons_append]

private def rightShiftEmb (w bW W : ℕ) (_hw : w ≤ W) : Fin W ↪ Fin (W + bW) :=
  ⟨fun i => if i.val < w
      then ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right W bW)⟩
      else ⟨i.val + bW, Nat.add_lt_add_right i.isLt bW⟩,
    fun i j hij => by
      have hv := congrArg Fin.val hij
      dsimp only at hv
      by_cases hi : i.val < w <;> by_cases hj : j.val < w <;>
        simp only [hi, hj, ↓reduceIte, Fin.val_mk] at hv <;> exact Fin.ext (by omega)⟩

@[simp]
private lemma rightShiftEmb_val (w bW W : ℕ) (hw : w ≤ W) (i : Fin W) :
    (rightShiftEmb w bW W hw i).val = if i.val < w then i.val else i.val + bW := by
  change (if i.val < w
      then (⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right W bW)⟩ : Fin (W + bW))
      else ⟨i.val + bW, Nat.add_lt_add_right i.isLt bW⟩).val =
    if i.val < w then i.val else i.val + bW
  split_ifs <;> rfl

private lemma right_foldl_instr {w bW W : ℕ} (hw : w ≤ W) (ins : Instr W) (revOut : List Bool) :
    (encInstr ins).foldl (fun b a => rightStep (b, a))
        (3, (List.replicate w true, (List.replicate w true, (List.replicate bW true, revOut)))) =
      (3, (List.replicate w true, (List.replicate w true, (List.replicate bW true,
        (encInstr (mapInstr (rightShiftEmb w bW W hw) ins)).reverse ++ revOut)))) := by
  have h1 := fun i r => right_foldl_compare w bW 8 9 3
    (fun e => by fin_cases e <;> rfl) rfl rfl (fun e => by fin_cases e <;> rfl)
    (fun e => by fin_cases e <;> rfl) (fun e => by fin_cases e <;> rfl)
    (fun e => by fin_cases e <;> rfl) rfl rfl rfl rfl
    (fun e => by fin_cases e <;> rfl) (fun e b => by fin_cases e <;> fin_cases b <;> rfl) i w r
  have h2 := fun i r => right_foldl_compare w bW 10 11 8
    (fun e => by fin_cases e <;> rfl) rfl rfl (fun e => by fin_cases e <;> rfl)
    (fun e => by fin_cases e <;> rfl) (fun e => by fin_cases e <;> rfl)
    (fun e => by fin_cases e <;> rfl) rfl rfl rfl rfl
    (fun e => by fin_cases e <;> rfl) (fun e b => by fin_cases e <;> fin_cases b <;> rfl) i w r
  have hite : ∀ (n : ℕ), (if w ≤ n then n + bW else n) = if n < w then n else n + bW := fun n => by
    split_ifs <;> omega
  cases ins with
  | h i =>
      change ([false] ++ encNat i.val).foldl (fun b a => rightStep (b, a)) _ = _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hs : rightStep ((3, (List.replicate w true, (List.replicate w true,
          (List.replicate bW true, revOut)))), false) =
          (8, (List.replicate w true, (List.replicate w true,
            (List.replicate bW true, false :: revOut)))) := by
        simp [rightStep, rightNext, rightShiftNow, rightResetW, rightPopW]
      rw [hs, h1 i.val (false :: revOut), hite]
      simp [encInstr, encNat, mapInstr, List.append_assoc]
  | s i =>
      change ([true, false] ++ encNat i.val).foldl (fun b a => rightStep (b, a)) _ = _
      rw [List.foldl_append]
      have hs : ([true, false]).foldl (fun b a => rightStep (b, a))
            (3, (List.replicate w true, (List.replicate w true, (List.replicate bW true, revOut)))) =
          (8, (List.replicate w true, (List.replicate w true,
            (List.replicate bW true, false :: true :: revOut)))) := by
        simp [rightStep, rightNext, rightShiftNow, rightResetW, rightPopW]
      rw [hs, h1 i.val (false :: true :: revOut), hite]
      simp [encInstr, encNat, mapInstr, List.append_assoc]
  | t i =>
      change ([true, true, false] ++ encNat i.val).foldl (fun b a => rightStep (b, a)) _ = _
      rw [List.foldl_append]
      have hs : ([true, true, false]).foldl (fun b a => rightStep (b, a))
            (3, (List.replicate w true, (List.replicate w true, (List.replicate bW true, revOut)))) =
          (8, (List.replicate w true, (List.replicate w true,
            (List.replicate bW true, false :: true :: true :: revOut)))) := by
        simp [rightStep, rightNext, rightShiftNow, rightResetW, rightPopW]
      rw [hs, h1 i.val (false :: true :: true :: revOut), hite]
      simp [encInstr, encNat, mapInstr, List.append_assoc]
  | x i =>
      change ([true, true, true, false] ++ encNat i.val).foldl (fun b a => rightStep (b, a)) _ = _
      rw [List.foldl_append]
      have hs : ([true, true, true, false]).foldl (fun b a => rightStep (b, a))
            (3, (List.replicate w true, (List.replicate w true, (List.replicate bW true, revOut)))) =
          (8, (List.replicate w true, (List.replicate w true,
            (List.replicate bW true, false :: true :: true :: true :: revOut)))) := by
        simp [rightStep, rightNext, rightShiftNow, rightResetW, rightPopW]
      rw [hs, h1 i.val (false :: true :: true :: true :: revOut), hite]
      simp [encInstr, encNat, mapInstr, List.append_assoc]
  | cnot i j hij =>
      change ([true, true, true, true, false] ++ encNat i.val ++ encNat j.val).foldl
        (fun b a => rightStep (b, a)) _ = _
      rw [List.foldl_append, List.foldl_append]
      have hs : ([true, true, true, true, false]).foldl (fun b a => rightStep (b, a))
            (3, (List.replicate w true, (List.replicate w true, (List.replicate bW true, revOut)))) =
          (10, (List.replicate w true, (List.replicate w true,
            (List.replicate bW true, false :: true :: true :: true :: true :: revOut)))) := by
        simp [rightStep, rightNext, rightShiftNow, rightResetW, rightPopW]
      rw [hs, h2 i.val (false :: true :: true :: true :: true :: revOut), h1 j.val _, hite, hite]
      simp [encInstr, encNat, mapInstr, List.append_assoc]

private lemma right_foldl_layer {w bW W : ℕ} (hw : w ≤ W) (cl : List (Instr W))
    (revOut : List Bool) :
    (cl.map encInstr).flatten.foldl (fun b a => rightStep (b, a))
        (3, (List.replicate w true, (List.replicate w true, (List.replicate bW true, revOut)))) =
      (3, (List.replicate w true, (List.replicate w true, (List.replicate bW true,
        ((mapCirc (rightShiftEmb w bW W hw) cl).map encInstr).flatten.reverse ++ revOut)))) := by
  induction cl generalizing revOut with
  | nil => simp [mapCirc]
  | cons ins cl ih =>
      simp only [List.map_cons, List.flatten_cons, List.foldl_append, mapCirc, List.reverse_append,
        List.append_assoc]
      rw [right_foldl_instr hw ins revOut, ih]
      simp [mapCirc]

private lemma shiftRightFun_correct {w bW W : ℕ} (hw : w ≤ W) (cl : List (Instr W)) :
    shiftRightFun (encNat w, (encNat bW, encNat W ++ encLayer cl)) =
      encNat (W + bW) ++ encLayer (mapCirc (rightShiftEmb w bW W hw) cl) := by
  simp only [shiftRightFun, takeWhile_encNat, encLayer, encStr, mapCirc, List.length_map]
  have hW := right_foldl_shift_encNat w bW W 0 1 2
    (fun e => by fin_cases e <;> rfl) (fun e => by fin_cases e <;> rfl)
    (fun e => by fin_cases e <;> rfl) (fun e => by fin_cases e <;> rfl)
    (fun e => by fin_cases e <;> rfl) (fun e => by fin_cases e <;> rfl)
    (fun b => by fin_cases b <;> rfl) (fun b => by fin_cases b <;> rfl)
    (fun e b => by fin_cases e <;> fin_cases b <;> rfl)
    (fun e b => by fin_cases e <;> fin_cases b <;> rfl) []
  have hlen := right_foldl_copy_encNat w bW cl.length 2 3
    (fun e => by fin_cases e <;> rfl) (fun e => by fin_cases e <;> rfl)
    (fun e => by fin_cases e <;> rfl) (fun b => by fin_cases b <;> rfl)
    (fun e b => by fin_cases e <;> fin_cases b <;> rfl) ((encNat (W + bW)).reverse ++ [])
  have hlay := right_foldl_layer (bW := bW) hw cl
    ((encNat cl.length).reverse ++ ((encNat (W + bW)).reverse ++ []))
  simp only [List.foldl_append]
  rw [hW, hlen, hlay]
  simp [mapCirc, List.append_assoc]

/-! ### Part 3: Circuit unitary and `Implements` preservation under right framing -/

private def splitRightQ (w bW W : ℕ) (hw : w ≤ W) : Qubits (W + bW) ≃ Qubits bW × Qubits W where
  toFun z :=
    (fun j => z ⟨w + j.val, by omega⟩, fun i => z (rightShiftEmb w bW W hw i))
  invFun p k :=
    if h1 : k.val < w then p.2 ⟨k.val, by omega⟩
    else if h2 : k.val < w + bW then p.1 ⟨k.val - w, by omega⟩
    else p.2 ⟨k.val - bW, by omega⟩
  left_inv z := by
    funext k
    by_cases h1 : k.val < w
    · simp only [dif_pos h1]
      congr 1
      ext
      simp [h1]
    · by_cases h2 : k.val < w + bW
      · simp only [dif_neg h1, dif_pos h2]
        congr 1
        ext
        dsimp only [Fin.val_mk]
        omega
      · simp only [dif_neg h1, dif_neg h2]
        congr 1
        ext
        have hlt : ¬ (k.val - bW < w) := by omega
        simp only [rightShiftEmb_val, if_neg hlt]
        omega
  right_inv p := by
    rcases p with ⟨qb, qw⟩
    ext x
    · simp only [dif_neg (show ¬ (w + x.val < w) by omega),
        dif_pos (show w + x.val < w + bW by omega)]
      congr 1
      ext
      dsimp only [Fin.val_mk]
      omega
    · by_cases hx : x.val < w
      · have hx' : (rightShiftEmb w bW W hw x).val < w := by simp [hx]
        simp only [dif_pos hx']
        congr 1
        ext
        simp [hx]
      · have h1 : ¬ ((rightShiftEmb w bW W hw x).val < w) := by simp [hx]; omega
        have h2 : ¬ ((rightShiftEmb w bW W hw x).val < w + bW) := by simp [hx]
        simp only [dif_neg h1, dif_neg h2]
        congr 1
        ext
        simp [hx]

private def liftRight (w bW W : ℕ) (hw : w ≤ W) (U : Matrix (Qubits W) (Qubits W) ℂ) :
    Matrix (Qubits (W + bW)) (Qubits (W + bW)) ℂ :=
  Matrix.of fun y z =>
    if (splitRightQ w bW W hw y).1 = (splitRightQ w bW W hw z).1
    then U (splitRightQ w bW W hw y).2 (splitRightQ w bW W hw z).2
    else 0

private lemma liftRight_one (w bW W : ℕ) (hw : w ≤ W) :
    liftRight w bW W hw 1 = 1 := by
  ext y z
  simp only [liftRight, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · have hsp : splitRightQ w bW W hw y ≠ splitRightQ w bW W hw z :=
      fun h => hyz ((splitRightQ w bW W hw).injective h)
    rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso; exact hsp (Prod.ext h1 h2)
    · rfl
    · rfl

private lemma liftRight_mul (w bW W : ℕ) (hw : w ≤ W)
    (A B : Matrix (Qubits W) (Qubits W) ℂ) :
    liftRight w bW W hw (A * B) = liftRight w bW W hw A * liftRight w bW W hw B := by
  ext y z
  simp only [liftRight, Matrix.of_apply, Matrix.mul_apply]
  rw [← (splitRightQ w bW W hw).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  by_cases h1 : (splitRightQ w bW W hw y).1 = (splitRightQ w bW W hw z).1
  · rw [if_pos h1, h1]
    rw [Finset.sum_eq_single (splitRightQ w bW W hw z).1]
    · simp only [↓reduceIte]
    · intro x _ hx
      rw [Finset.sum_eq_zero]
      intro u _
      simp [Ne.symm hx]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [if_neg h1]
    symm
    rw [Finset.sum_eq_zero]
    intro x _
    rw [Finset.sum_eq_zero]
    intro u _
    by_cases hx1 : (splitRightQ w bW W hw y).1 = x
    · have hx2 : x ≠ (splitRightQ w bW W hw z).1 := fun h => h1 (hx1.trans h)
      simp [hx2]
    · simp [hx1]

private lemma liftRight_list_prod (w bW W : ℕ) (hw : w ≤ W)
    (ms : List (Matrix (Qubits W) (Qubits W) ℂ)) :
    (ms.map (liftRight w bW W hw)).prod = liftRight w bW W hw ms.prod := by
  induction ms with
  | nil => simp [liftRight_one]
  | cons m ms ih => simp [ih, liftRight_mul]

private lemma embedOp_rightShiftEmb {k w bW W : ℕ} (hw : w ≤ W)
    (M : Matrix (Qubits k) (Qubits k) ℂ) (v : Fin k ↪ Fin W) :
    embedOp M (v.trans (rightShiftEmb w bW W hw)) = liftRight w bW W hw (embedOp M v) := by
  ext y z
  let e := rightShiftEmb w bW W hw
  simp only [embedOp, liftRight, Matrix.of_apply]
  have hiff :
      (∀ a : Fin (W + bW), a ∉ Set.range (v.trans e) → y a = z a) ↔
      ((splitRightQ w bW W hw y).1 = (splitRightQ w bW W hw z).1 ∧
       ∀ b : Fin W, b ∉ Set.range v →
         (splitRightQ w bW W hw y).2 b = (splitRightQ w bW W hw z).2 b) := by
    constructor
    · intro h
      refine ⟨funext fun j => h ⟨w + j.val, by omega⟩ ?_, fun b hb => h (e b) ?_⟩
      · rintro ⟨x, hx⟩
        have hval := congrArg Fin.val hx
        simp only [Function.Embedding.trans_apply, e, rightShiftEmb_val] at hval
        split_ifs at hval <;> omega
      · rintro ⟨x, hx⟩
        apply hb
        exact ⟨x, e.injective hx⟩
    · rintro ⟨h1, h2⟩ a ha
      by_cases ha1 : a.val < w
      · have ha_eq : a = e ⟨a.val, by omega⟩ := by
          ext; simp [e, ha1]
        rw [ha_eq] at ha ⊢
        apply h2 ⟨a.val, by omega⟩
        rintro ⟨x, hxv⟩
        exact ha ⟨x, congrArg e hxv⟩
      · by_cases ha2 : a.val < w + bW
        · have ha_eq : a = ⟨w + (a.val - w), by omega⟩ := by ext; dsimp only [Fin.val_mk]; omega
          rw [ha_eq]
          exact congrFun h1 ⟨a.val - w, by omega⟩
        · have hge : ¬ (a.val - bW < w) := by omega
          have ha_eq : a = e ⟨a.val - bW, by omega⟩ := by
            ext; simp [e, hge]; omega
          rw [ha_eq] at ha ⊢
          apply h2 ⟨a.val - bW, by omega⟩
          rintro ⟨x, hxv⟩
          exact ha ⟨x, congrArg e hxv⟩
  have hcomp : y ∘ (v.trans e) = (splitRightQ w bW W hw y).2 ∘ v := by
    funext x; rfl
  have hcompz : z ∘ (v.trans e) = (splitRightQ w bW W hw z).2 ∘ v := by
    funext x; rfl
  by_cases hc : ∀ a : Fin (W + bW), a ∉ Set.range (v.trans e) → y a = z a
  · obtain ⟨h1, h2⟩ := hiff.mp hc
    rw [if_pos hc, if_pos h1, if_pos h2, hcomp, hcompz]
  · rw [if_neg hc]
    by_cases h1 : (splitRightQ w bW W hw y).1 = (splitRightQ w bW W hw z).1
    · rw [if_pos h1]
      have h2 : ¬ ∀ b : Fin W, b ∉ Set.range v →
          (splitRightQ w bW W hw y).2 b = (splitRightQ w bW W hw z).2 b :=
        fun hb => hc (hiff.mpr ⟨h1, hb⟩)
      rw [if_neg h2]
    · rw [if_neg h1]

private lemma instrApp_mapInstr {m n : ℕ} (e : Fin m ↪ Fin n) (ins : Instr m) :
    embedOp (instrApp (mapInstr e ins)).gate.mat (instrApp (mapInstr e ins)).wires =
      embedOp (instrApp ins).gate.mat ((instrApp ins).wires.trans e) := by
  cases ins with
  | h i | s i | t i | x i =>
      simp only [mapInstr, instrApp]
      congr 1
  | cnot i j hij =>
      simp only [mapInstr, instrApp]
      congr 1
      ext a
      fin_cases a <;> rfl

private lemma circUnitary_rightShiftCirc (w bW W : ℕ) (hw : w ≤ W) (cl : List (Instr W)) :
    circUnitary (mapCirc (rightShiftEmb w bW W hw) cl) =
      liftRight w bW W hw (circUnitary cl) := by
  simp only [circUnitary, Circuit.unitary, mapCirc, List.map_map]
  have hmap :
      List.map ((fun g : GateApp cliffordT (W + bW) => embedOp g.gate.mat g.wires) ∘
          instrApp ∘ mapInstr (rightShiftEmb w bW W hw)) cl =
      (List.map ((fun g : GateApp cliffordT W => embedOp g.gate.mat g.wires) ∘ instrApp) cl).map
        (liftRight w bW W hw) := by
    rw [List.map_map]
    refine List.map_congr_left fun ins _ => ?_
    simp only [Function.comp_apply, instrApp_mapInstr, embedOp_rightShiftEmb]
  rw [hmap, ← List.map_reverse, liftRight_list_prod]

private lemma padTo_appendCode_right {X B : Type} {w bW W : ℕ} (hw : w ≤ W)
    (cin : X → Qubits w) (cb : B → Qubits bW) (x : X) (b : B) :
    padTo (W + bW) (appendCode cin cb (x, b)) =
      (splitRightQ w bW W hw).symm (cb b, padTo W (cin x)) := by
  apply (splitRightQ w bW W hw).injective
  rw [Equiv.apply_symm_apply]
  ext k
  · simp only [splitRightQ, Equiv.coe_fn_mk, padTo, appendCode]
    have hk : w + k.val < w + bW := by omega
    rw [dif_pos hk]
    have hcast : (⟨w + k.val, hk⟩ : Fin (w + bW)) = Fin.natAdd w k := by ext; rfl
    rw [hcast, Fin.append_right]
  · simp only [splitRightQ, Equiv.coe_fn_mk, padTo, appendCode, rightShiftEmb_val]
    by_cases hk : k.val < w
    · simp only [if_pos hk]
      have hk' : k.val < w + bW := by omega
      rw [dif_pos hk', dif_pos hk]
      have hcast : (⟨k.val, hk'⟩ : Fin (w + bW)) = Fin.castAdd bW ⟨k.val, hk⟩ := by ext; rfl
      rw [hcast, Fin.append_left]
    · simp only [if_neg hk]
      have hk' : ¬ (k.val + bW < w + bW) := by omega
      rw [dif_neg hk', dif_neg hk]

private lemma implements_frame_right {X Y B : Type} [Fintype X] [Fintype Y] [Fintype B]
    [DecidableEq B] {w bW W : ℕ} {cin : X → Qubits w} {cout : Y → Qubits w}
    {cb : B → Qubits bW} {U : Matrix (Qubits W) (Qubits W) ℂ} {Φ : Matrix Y X ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hw : w ≤ W) (hcb : Function.Injective cb)
    (himp : Implements U (fun x => padTo W (cin x)) (fun y => padTo W (cout y)) Φ ε) :
    Implements (liftRight w bW W hw U)
      (fun p => padTo (W + bW) (appendCode cin cb p))
      (fun p => padTo (W + bW) (appendCode cout cb p))
      (frameMatRight Φ) ε := by
  intro ψ
  let ψb : B → EuclideanSpace ℂ X := fun b => WithLp.toLp 2 (fun x => ψ (x, b))
  let diff : EuclideanSpace ℂ (Qubits (W + bW)) :=
    act (liftRight w bW W hw U) (embedVec (fun p => padTo (W + bW) (appendCode cin cb p)) ψ) -
      embedVec (fun p => padTo (W + bW) (appendCode cout cb p))
        (WithLp.toLp 2 ((frameMatRight Φ).mulVec (WithLp.ofLp ψ)))
  let err : B → EuclideanSpace ℂ (Qubits W) := fun b =>
    act U (embedVec (fun x => padTo W (cin x)) (ψb b)) -
      embedVec (fun y => padTo W (cout y)) (WithLp.toLp 2 (Φ.mulVec (WithLp.ofLp (ψb b))))
  let mkR : Qubits bW → Qubits W → Qubits (W + bW) := fun q1 q2 =>
    (splitRightQ w bW W hw).symm (q1, q2)
  have hact_eq : ∀ (q1 : Qubits bW) (q2 : Qubits W),
      act (liftRight w bW W hw U)
        (embedVec (fun p => padTo (W + bW) (appendCode cin cb p)) ψ) (mkR q1 q2) =
      ∑ b : B, if cb b = q1 then act U (embedVec (fun x => padTo W (cin x)) (ψb b)) q2 else 0 := by
    intro q1 q2
    simp only [act, Matrix.mulVec, dotProduct, embedVec, WithLp.ofLp_toLp]
    rw [← (splitRightQ w bW W hw).symm.sum_comp, Fintype.sum_prod_type]
    have hsplit : ∀ (z1 : Qubits bW) (z2 : Qubits W),
        (∑ x : X × B, if padTo (W + bW) (appendCode cin cb x) = mkR z1 z2 then ψ x else 0) =
        ∑ b : B, if cb b = z1 then ∑ x : X, if padTo W (cin x) = z2 then ψ (x, b) else 0 else 0 := by
      intro z1 z2
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : cb b = z1
      · rw [if_pos hb]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [padTo_appendCode_right hw, hb]
        have hinj : (mkR z1 (padTo W (cin x)) = mkR z1 z2) ↔ (padTo W (cin x) = z2) := by
          constructor
          · intro h; exact (Prod.ext_iff.mp ((splitRightQ w bW W hw).symm.injective h)).2
          · intro h; rw [h]
        simp [mkR, hinj]
      · rw [if_neg hb, Finset.sum_eq_zero]
        intro x _
        rw [padTo_appendCode_right hw]
        have hne : mkR (cb b) (padTo W (cin x)) ≠ mkR z1 z2 := by
          intro h
          exact hb (Prod.ext_iff.mp ((splitRightQ w bW W hw).symm.injective h)).1
        rw [if_neg hne]
    simp only [liftRight, Matrix.of_apply, mkR, Equiv.apply_symm_apply]
    rw [Finset.sum_eq_single q1]
    · simp only [↓reduceIte]
      have hsum_y : ∀ y : Qubits W,
          U q2 y * (∑ x : X × B,
            if padTo (W + bW) (appendCode cin cb x) = mkR q1 y then ψ x else 0) =
          U q2 y * (∑ b : B, if cb b = q1 then
            ∑ x : X, if padTo W (cin x) = y then ψ (x, b) else 0 else 0) :=
        fun y => congrArg (U q2 y * ·) (hsplit q1 y)
      calc
        (∑ y : Qubits W, U q2 y * (∑ x : X × B,
            if padTo (W + bW) (appendCode cin cb x) = mkR q1 y then ψ x else 0))
            = ∑ y : Qubits W, U q2 y * (∑ b : B, if cb b = q1 then
                ∑ x : X, if padTo W (cin x) = y then ψ (x, b) else 0 else 0) :=
              Finset.sum_congr rfl fun y _ => hsum_y y
        _ = ∑ b : B, if cb b = q1 then ∑ y : Qubits W, U q2 y *
                ∑ x : X, if padTo W (cin x) = y then (ψb b) x else 0 else 0 := by
              simp only [Finset.mul_sum, mul_ite, mul_zero]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => ?_
              split_ifs with hb
              · rfl
              · simp
    · intro z1 _ hz1
      simp [Ne.symm hz1]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hout_eq : ∀ (q1 : Qubits bW) (q2 : Qubits W),
      embedVec (fun p => padTo (W + bW) (appendCode cout cb p))
        (WithLp.toLp 2 ((frameMatRight Φ).mulVec (WithLp.ofLp ψ))) (mkR q1 q2) =
      ∑ b : B, if cb b = q1 then
        embedVec (fun y => padTo W (cout y)) (WithLp.toLp 2 (Φ.mulVec (WithLp.ofLp (ψb b)))) q2
      else 0 := by
    intro q1 q2
    simp only [embedVec, WithLp.ofLp_toLp, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : cb b = q1
    · rw [if_pos hb]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [padTo_appendCode_right hw, hb]
      by_cases hy : padTo W (cout y) = q2
      · have hmk : mkR q1 (padTo W (cout y)) = mkR q1 q2 := by rw [hy]
        rw [if_pos hmk, if_pos hy]
        simp only [Matrix.mulVec, dotProduct, frameMatRight, Matrix.of_apply, Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        rw [Finset.sum_eq_single b]
        · simp [ψb]
        · intro x _ hx; simp [Ne.symm hx]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · have hne : mkR q1 (padTo W (cout y)) ≠ mkR q1 q2 := by
          intro h
          exact hy (Prod.ext_iff.mp ((splitRightQ w bW W hw).symm.injective h)).2
        rw [if_neg hne, if_neg hy]
    · rw [if_neg hb, Finset.sum_eq_zero]
      intro y _
      rw [padTo_appendCode_right hw]
      have hne : mkR (cb b) (padTo W (cout y)) ≠ mkR q1 q2 := by
        intro h
        exact hb (Prod.ext_iff.mp ((splitRightQ w bW W hw).symm.injective h)).1
      rw [if_neg hne]
  have hdiff_eq : ∀ (q1 : Qubits bW) (q2 : Qubits W),
      diff (mkR q1 q2) = ∑ b : B, if cb b = q1 then err b q2 else 0 := by
    intro q1 q2
    change act (liftRight w bW W hw U) _ (mkR q1 q2) - embedVec _ _ (mkR q1 q2) = _
    rw [hact_eq, hout_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp [err]
  have hnorm_sq : ‖diff‖ ^ 2 = ∑ b : B, ‖err b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [← (splitRightQ w bW W hw).symm.sum_comp, Fintype.sum_prod_type]
    have hq1 : ∀ q1 : Qubits bW,
        (∑ q2 : Qubits W, ‖diff (mkR q1 q2)‖ ^ 2) =
        ∑ b : B, if cb b = q1 then ‖err b‖ ^ 2 else 0 := by
      intro q1
      by_cases hex : ∃ b : B, cb b = q1
      · obtain ⟨b0, hb0⟩ := hex
        have huniq : ∀ b : B, cb b = q1 ↔ b = b0 := fun b =>
          ⟨fun h => hcb (h.trans hb0.symm), fun h => h ▸ hb0⟩
        simp_rw [mkR] at hdiff_eq ⊢
        simp_rw [hdiff_eq, huniq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [EuclideanSpace.norm_sq_eq]
      · have hzero : ∀ b : B, cb b ≠ q1 := fun b h => hex ⟨b, h⟩
        have hsum0 : ∀ q2 : Qubits W, (∑ b : B, if cb b = q1 then err b q2 else 0) = 0 := fun q2 =>
          Finset.sum_eq_zero fun b _ => if_neg (hzero b)
        simp_rw [mkR] at hdiff_eq ⊢
        simp_rw [hdiff_eq, hsum0]
        simp [hzero]
    simp_rw [mkR] at hq1
    simp_rw [hq1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp
  have hpsi_sq : ‖ψ‖ ^ 2 = ∑ b : B, ‖ψb b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
  have hsq_le : ‖diff‖ ^ 2 ≤ (ε * ‖ψ‖) ^ 2 := by
    rw [hnorm_sq, mul_pow, hpsi_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have hb := himp (ψb b)
    have hsq := sq_le_sq' (by linarith [norm_nonneg (err b)]) hb
    simpa [mul_pow] using hsq
  have hle : ‖diff‖ ≤ ε * ‖ψ‖ := by
    nlinarith [norm_nonneg diff, mul_nonneg hε (norm_nonneg ψ)]
  exact hle

theorem frame_right_proof
    {P : FieldData → Prop} {X Y B : FieldData → Type}
    [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] [∀ D, Fintype (B D)] [∀ D, DecidableEq (B D)]
    {w bW : FieldData → ℕ}
    {cin : ∀ D, X D → Qubits (w D)}
    {cout : ∀ D, Y D → Qubits (w D)}
    (cb : ∀ D, B D → Qubits (bW D))
    {Φ : ∀ D, Matrix (Y D) (X D) ℂ}
    (h : UniformlyImplementsOn P cin cout Φ)
    (hcb : ∀ D, P D → Function.Injective (cb D))
    (hw : ∃ fw : Str → Str, PolyTimeComputable fw ∧ ∀ D, P D → fw D.encData = encNat (w D))
    (hbw : ∃ fb : Str → Str, PolyTimeComputable fb ∧ ∀ D, P D → fb D.encData = encNat (bW D)) :
    UniformlyImplementsOn P
      (fun D => appendCode (cin D) (cb D))
      (fun D => appendCode (cout D) (cb D))
      (fun D => frameMatRight (Φ D)) := by
  obtain ⟨wires, circ, f, c, hf, hf_eq, hlen, himp⟩ := h
  obtain ⟨fw, hfw, hfw_eq⟩ := hw
  obtain ⟨fb, hfb, hfb_eq⟩ := hbw
  have hcomp_fw : PolyTimeComputable (fw ∘ extractData) := by
    obtain ⟨mfw⟩ := hfw
    exact Turing.TM2ComputableInPolyTime.comp_of_polytime extractDataProgram.stock mfw
  have hcomp_fb : PolyTimeComputable (fb ∘ extractData) := by
    obtain ⟨mfb⟩ := hfb
    exact Turing.TM2ComputableInPolyTime.comp_of_polytime extractDataProgram.stock mfb
  obtain ⟨m23⟩ := polyTimeComputable_fanout hcomp_fb hf
  let g23 : Str → Str := fun x => encodePair (id : Str → Str) (id : Str → Str) (fb (extractData x), f x)
  have hg23 : PolyTimeComputable g23 := ⟨{
    tm := m23.tm
    inputAlphabet := m23.inputAlphabet
    outputAlphabet := m23.outputAlphabet
    time := m23.time
    outputsFun := fun x => m23.outputsFun x
  }⟩
  obtain ⟨m123⟩ := polyTimeComputable_fanout hcomp_fw hg23
  let m123' : Turing.TM2ComputableInPolyTime (id : Str → Str)
      (encodePair (id : Str → Str) (encodePair (id : Str → Str) (id : Str → Str)))
      (fun x : Str => (fw (extractData x), (fb (extractData x), f x))) := {
    tm := m123.tm
    inputAlphabet := m123.inputAlphabet
    outputAlphabet := m123.outputAlphabet
    time := m123.time
    outputsFun := fun x => by
      simpa [g23, encodePair] using m123.outputsFun x
  }
  obtain ⟨mf'⟩ := Turing.TM2ComputableInPolyTime.comp_of_polytime m123' shiftRightProgram.stock
  let circ' : ∀ D k, List (Instr (wires D k + bW D)) := fun D k =>
    if hwk : w D ≤ wires D k then
      mapCirc (rightShiftEmb (w D) (bW D) (wires D k) hwk) (circ D k)
    else []
  refine ⟨fun D k => wires D k + bW D, circ',
    shiftRightFun ∘ (fun x => (fw (extractData x), (fb (extractData x), f x))), c, ⟨mf'⟩, ?_, ?_, ?_⟩
  · intro D hP k
    have hwk : w D ≤ wires D k := (himp D hP k).1
    simp only [Function.comp_apply, extractData_encData, hfw_eq D hP, hfb_eq D hP, hf_eq D hP k,
      circ', dif_pos hwk]
    exact shiftRightFun_correct hwk (circ D k)
  · intro D hP k
    have hwk : w D ≤ wires D k := (himp D hP k).1
    simp only [circ', dif_pos hwk, mapCirc, List.length_map]
    exact hlen D hP k
  · intro D hP k
    obtain ⟨hin, hout, hU⟩ := himp D hP k
    refine ⟨Nat.add_le_add_right hin _, Nat.add_le_add_right hout _, ?_⟩
    simp only [circ', dif_pos hin]
    rw [circUnitary_rightShiftCirc]
    exact implements_frame_right (by positivity) hin (hcb D hP) hU

end GL2QFT_FrameRight_Aux

theorem solution
    {P : GL2QFT.FieldData → Prop} {X Y B : GL2QFT.FieldData → Type}
    [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] [∀ D, Fintype (B D)] [∀ D, DecidableEq (B D)]
    {w bW : GL2QFT.FieldData → ℕ}
    {cin : ∀ D, X D → QAlgorithms.Qubits (w D)}
    {cout : ∀ D, Y D → QAlgorithms.Qubits (w D)}
    (cb : ∀ D, B D → QAlgorithms.Qubits (bW D))
    {Φ : ∀ D, Matrix (Y D) (X D) ℂ}
    (h : GL2QFT.UniformlyImplementsOn P cin cout Φ)
    (hcb : ∀ D, P D → Function.Injective (cb D))
    (hw : ∃ fw : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str,
      QAlgorithms.Complexity.PolyTimeComputable fw ∧
      ∀ D, P D → fw D.encData = QAlgorithms.Complexity.encNat (w D))
    (hbw : ∃ fb : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str,
      QAlgorithms.Complexity.PolyTimeComputable fb ∧
      ∀ D, P D → fb D.encData = QAlgorithms.Complexity.encNat (bW D)) :
    GL2QFT.UniformlyImplementsOn P
      (fun D => GL2QFT.Circuits.appendCode (cin D) (cb D))
      (fun D => GL2QFT.Circuits.appendCode (cout D) (cb D))
      (fun D => GL2QFT.Circuits.frameMatRight (Φ D)) :=
  GL2QFT_FrameRight_Aux.frame_right_proof cb h hcb hw hbw
