-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_frame
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:50:29.686829+00:00
-- url     : https://prove2.me/submissions/21aff624-ebec-4fa3-b807-0dcfd5ddf4fa

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_Turing_TM2ComputableInPolyTime_comp_of_polytime
import Theorems.Thm_QAlgorithms_DeWolf_clocked_tm2_polytime

set_option autoImplicit false

noncomputable section

open Classical
open scoped BigOperators

namespace GL2QFT_Frame_Aux

open GL2QFT GL2QFT.Circuits QAlgorithms QAlgorithms.Complexity
open OAI.MetricKMedian.Binary

/-! ### Part 1: PolyTimeComputable combinators (`comp`, `thread`, `fanout`) -/

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
    letI := M.tm.kDecidableEq
    Trace (Turing.TM2.step (tCode M)) (xs.length + 1)
      ⟨some (.inr 0), (M.tm.initialState, none), tStore (fun _ => []) (quote xs ++ tail) buf⟩
      ⟨some (.inr 1), (M.tm.initialState, none), tStore (fun _ => []) tail (xs.reverse ++ buf)⟩ := by
  letI := M.tm.kDecidableEq
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
    letI := M.tm.kDecidableEq
    Trace (Turing.TM2.step (tCode M)) (buf.length + 1)
      ⟨some (.inr 1), (M.tm.initialState, none),
        tStore (Function.update (fun _ => []) M.tm.k₀ ys) tail buf⟩
      ⟨some (.inl M.tm.main), (M.tm.initialState, none),
        tStore (Function.update (fun _ => []) M.tm.k₀ (buf.reverse.map M.inputAlphabet.invFun ++ ys)) tail []⟩ := by
  letI := M.tm.kDecidableEq
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
    letI := M.tm.kDecidableEq
    Trace (Turing.TM2.step (tCode M)) n (tEmbedCfg M.tm tail a) (tEmbedCfg M.tm tail b) := by
  letI := M.tm.kDecidableEq
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
    letI := M.tm.kDecidableEq
    ∃ s' : ∀ k, List (M.tm.Γ k),
      Trace (Turing.TM2.step (tCode M)) (zs.length + 1)
        ⟨some (.inr 2), (M.tm.initialState, none), tStore s tail buf⟩
        ⟨some (.inr 3), (M.tm.initialState, none), tStore s' tail ((quote zs).reverse ++ buf)⟩ := by
  letI := M.tm.kDecidableEq
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
    letI := M.tm.kDecidableEq
    Trace (Turing.TM2.step (tCode M)) (buf.length + 1)
      ⟨some (.inr 3), (M.tm.initialState, none), tStore s tail buf⟩
      ⟨none, (M.tm.initialState, none), tStore s (buf.reverse ++ tail) []⟩ := by
  letI := M.tm.kDecidableEq
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
  letI := M.tm.kDecidableEq
  letI := M.tm.kFin
  letI := M.tm.ΛFin
  letI := M.tm.σFin
  letI : Inhabited (@Sum.elim M.tm.K Bool Type M.tm.Γ (fun _ => Bool) (.inr false)) := ⟨false⟩
  letI : Fintype (@Sum.elim M.tm.K Bool Type M.tm.Γ (fun _ => Bool) (.inr false)) :=
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

/-! ### Part 2: Pure PolyPrograms for extracting `D.encData`, extracting `onesA`, and shifting `encLayer` -/

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

private def frameNext (x : Fin 12 × Bool) : Fin 12 :=
  match x.1.val, x.2 with
  | 0, true => 1
  | 0, false => 2
  | 1, true => 1
  | 1, false => 2
  | 2, true => 2
  | 2, false => 3
  | 3, true => 4
  | 3, false => 8
  | 4, true => 5
  | 4, false => 8
  | 5, true => 6
  | 5, false => 8
  | 6, true => 7
  | 6, false => 8
  | 7, true => 7
  | 7, false => 10
  | 8, true => 9
  | 8, false => 3
  | 9, true => 9
  | 9, false => 3
  | 10, true => 11
  | 10, false => 8
  | 11, true => 11
  | 11, false => 8
  | _, _ => 0

private def frameShouldShift (p : Fin 12) : Bool :=
  p == 0 || p == 8 || p == 10

private abbrev FrameAcc := Fin 12 × (List Bool × List Bool)

private abbrev ebFrame : FrameAcc → List Bool :=
  encodePair encFin12 (encodePair (id : Str → Str) (id : Str → Str))

private def frameStep (x : FrameAcc × Bool) : FrameAcc :=
  let s := x.1
  let b := x.2
  (frameNext (s.1, b), (s.2.1, b :: (if frameShouldShift s.1 then s.2.1 ++ s.2.2 else s.2.2)))

private noncomputable def frameStepProgram :
    PolyProgram (encodePair ebFrame encodeBool) ebFrame frameStep := by
  let ps := PolyProgram.fst ebFrame encodeBool
  let pb := PolyProgram.snd ebFrame encodeBool
  let pp := ps.comp (PolyProgram.fst encFin12 (encodePair (id : Str → Str) (id : Str → Str)))
  let pro := ps.comp (PolyProgram.snd encFin12 (encodePair (id : Str → Str) (id : Str → Str)))
  let pr := pro.comp (PolyProgram.fst (id : Str → Str) (id : Str → Str))
  let po := pro.comp (PolyProgram.snd (id : Str → Str) (id : Str → Str))
  let nextP := (pp.fanout pb).comp
    (PolyProgram.boolFunction (encodePair encFin12 encodeBool) encFin12 frameNext
      (encodePair_injective encFin12_injective encodeBool_injective))
  let needS := pp.comp
    (PolyProgram.boolFunction encFin12 encodeBool frameShouldShift encFin12_injective)
  let appOut := (pr.fanout po).comp PolyProgram.append
  let emitTail := PolyProgram.ite needS po appOut
  let newOut := (pb.fanout emitTail).comp PolyProgram.cons
  exact (nextP.fanout (pr.fanout newOut)).congr _ (fun _ => rfl)

private lemma frameStep_bound (pre : List Bool) (s : FrameAcc) :
    (pre.foldl (fun b a => frameStep (b, a)) s).2.1 = s.2.1 ∧
    (pre.foldl (fun b a => frameStep (b, a)) s).2.2.length ≤
      s.2.2.length + pre.length * (1 + s.2.1.length) := by
  induction pre generalizing s with
  | nil => simp
  | cons b pre ih =>
      obtain ⟨h1, h2⟩ := ih (frameStep (s, b))
      refine ⟨h1, ?_⟩
      simp only [List.foldl_cons, List.length_cons]
      have hlen : (frameStep (s, b)).2.2.length ≤ s.2.2.length + (1 + s.2.1.length) := by
        simp only [frameStep, List.length_cons]
        split_ifs <;> simp <;> omega
      have hs1 : (frameStep (s, b)).2.1 = s.2.1 := rfl
      rw [hs1] at h2
      nlinarith

private noncomputable def shiftFrameFold :
    PolyProgram (encodePair (encodeList encodeBool) ebFrame) ebFrame
      (fun x => x.1.foldl (fun b a => frameStep (b, a)) x.2) :=
  PolyProgram.listFold frameStepProgram false (Polynomial.X ^ 2 + 2 * Polynomial.X + 26)
    (fun as s pre suf he => by
      obtain ⟨_, hlen⟩ := frameStep_bound pre s
      have hpre : pre.length ≤ as.length := by rw [he, List.length_append]; omega
      have has : as.length ≤ (encodeList encodeBool as).length := EncodedList.length_le encodeBool as
      have hf : (encFin12 (pre.foldl (fun b a => frameStep (b, a)) s).1).length ≤ 12 :=
        encFin12_length _
      have hr : (pre.foldl (fun b a => frameStep (b, a)) s).2.1 = s.2.1 :=
        (frameStep_bound pre s).1
      set L := (encodePair (encodeList encodeBool) ebFrame (as, s)).length
      have hL1 : (encodeList encodeBool as).length ≤ L := by
        dsimp [L]; simp [encodePair_length]; omega
      have hL2 : 2 * s.2.1.length + 1 + s.2.2.length ≤ L := by
        dsimp [L]; simp [ebFrame, encodePair_length]; omega
      simp only [ebFrame, encodePair_length, id_eq] at hf ⊢
      rw [hr]
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_ofNat]
      nlinarith)

private def shiftFrameFun (p : Str × Str) : Str :=
  let ones := p.1.takeWhile id
  let acc := p.2.foldl (fun b a => frameStep (b, a)) ((0 : Fin 12), (ones, []))
  acc.2.2.reverse

private noncomputable def shiftFrameProgram :
    PolyProgram (encodePair (id : Str → Str) (id : Str → Str)) id shiftFrameFun := by
  let ex := encodePair (id : Str → Str) (id : Str → Str)
  let p1 := PolyProgram.fst (id : Str → Str) (id : Str → Str)
  let p2 := PolyProgram.snd (id : Str → Str) (id : Str → Str)
  let ones := p1.comp (takeWhileTrueT.program.of_word (eb := id) (f := List.takeWhile id)
    takeWhileTrueT_run)
  let encS := p2.comp (toEncodedBoolListT.program.of_word (eb := encodeList encodeBool) (f := id)
    toEncodedBoolListT_run)
  let init := (PolyProgram.constant ex encFin12 (0 : Fin 12)).fanout
    (ones.fanout (PolyProgram.constant ex (id : Str → Str) []))
  let fld := (encS.fanout init).comp shiftFrameFold
  let getOut := fld.comp ((PolyProgram.snd encFin12 (encodePair (id : Str → Str) (id : Str → Str))).comp
    (PolyProgram.snd (id : Str → Str) (id : Str → Str)))
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

@[simp]
private lemma shiftEmb_val (off m n : ℕ) (h : off + m ≤ n) (i : Fin m) :
    (shiftEmb off m n h i).val = off + i.val := rfl

private lemma frame_foldl_shift_encNat (aW n : ℕ) (p0 p1 pDone : Fin 12)
    (h0t : frameNext (p0, true) = p1) (h0f : frameNext (p0, false) = pDone)
    (h1t : frameNext (p1, true) = p1) (h1f : frameNext (p1, false) = pDone)
    (hs0 : frameShouldShift p0 = true) (hs1 : frameShouldShift p1 = false)
    (revOut : List Bool) :
    (encNat n).foldl (fun b a => frameStep (b, a)) (p0, (List.replicate aW true, revOut)) =
      (pDone, (List.replicate aW true, (encNat (aW + n)).reverse ++ revOut)) := by
  have htail : ∀ (m : ℕ) (r : List Bool),
      (List.replicate m true ++ [false]).foldl (fun b a => frameStep (b, a))
        (p1, (List.replicate aW true, r)) =
        (pDone, (List.replicate aW true, false :: (List.replicate m true ++ r))) := by
    intro m r
    induction m generalizing r with
    | zero => simp [frameStep, hs1, h1f]
    | succ m ih =>
        rw [List.replicate_succ, List.cons_append, List.foldl_cons]
        have hstep : frameStep ((p1, (List.replicate aW true, r)), true) =
            (p1, (List.replicate aW true, true :: r)) := by
          simp [frameStep, hs1, h1t]
        rw [hstep, ih (true :: r)]
        rw [replicate_true_append_cons]
        rfl
  cases n with
  | zero =>
      simp [encNat, frameStep, hs0, h0f]
  | succ n =>
      rw [encNat, List.replicate_succ, List.cons_append, List.foldl_cons]
      have hfirst : frameStep ((p0, (List.replicate aW true, revOut)), true) =
          (p1, (List.replicate aW true, true :: (List.replicate aW true ++ revOut))) := by
        simp [frameStep, hs0, h0t]
      rw [hfirst, htail n]
      have hrep : List.replicate (aW + (n + 1)) true =
          List.replicate aW true ++ true :: List.replicate n true := by
        rw [show aW + (n + 1) = aW + (n + 1) by rfl, List.replicate_add, List.replicate_succ,
          replicate_true_append_cons]
      simp only [encNat, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.reverse_replicate, List.cons_append, Prod.mk.injEq, true_and]
      rw [hrep, List.append_assoc]
      exact congrArg (false :: ·) (replicate_true_assoc_eq n aW revOut)

private lemma frame_foldl_copy_encNat (aW n : ℕ) (p0 pDone : Fin 12)
    (ht : frameNext (p0, true) = p0) (hf : frameNext (p0, false) = pDone)
    (hs : frameShouldShift p0 = false) (revOut : List Bool) :
    (encNat n).foldl (fun b a => frameStep (b, a)) (p0, (List.replicate aW true, revOut)) =
      (pDone, (List.replicate aW true, (encNat n).reverse ++ revOut)) := by
  have haux : ∀ (m : ℕ) (r : List Bool),
      (List.replicate m true ++ [false]).foldl (fun b a => frameStep (b, a))
        (p0, (List.replicate aW true, r)) =
        (pDone, (List.replicate aW true, false :: (List.replicate m true ++ r))) := by
    intro m r
    induction m generalizing r with
    | zero => simp [frameStep, hs, hf]
    | succ m ih =>
        rw [List.replicate_succ, List.cons_append, List.foldl_cons]
        have hstep : frameStep ((p0, (List.replicate aW true, r)), true) =
            (p0, (List.replicate aW true, true :: r)) := by
          simp [frameStep, hs, ht]
        rw [hstep, ih (true :: r), replicate_true_append_cons]
        rfl
  simpa [encNat] using haux n revOut

private lemma frame_foldl_instr {aW W : ℕ} (ins : Instr W) (revOut : List Bool) :
    (encInstr ins).foldl (fun b a => frameStep (b, a)) (3, (List.replicate aW true, revOut)) =
      (3, (List.replicate aW true,
        (encInstr (mapInstr (shiftEmb aW W (aW + W) le_rfl) ins)).reverse ++ revOut)) := by
  have h1 := fun i r => frame_foldl_shift_encNat aW i 8 9 3 rfl rfl rfl rfl rfl rfl r
  have h2 := fun i r => frame_foldl_shift_encNat aW i 10 11 8 rfl rfl rfl rfl rfl rfl r
  cases ins with
  | h i =>
      change ([false] ++ encNat i.val).foldl (fun b a => frameStep (b, a)) _ = _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hs : frameStep ((3, (List.replicate aW true, revOut)), false) =
          (8, (List.replicate aW true, false :: revOut)) := by
        simp [frameStep, frameShouldShift, frameNext]
      rw [hs, h1 i.val (false :: revOut)]
      simp [encInstr, encNat, mapInstr, List.append_assoc]
  | s i =>
      change ([true, false] ++ encNat i.val).foldl (fun b a => frameStep (b, a)) _ = _
      rw [List.foldl_append]
      have hs : ([true, false]).foldl (fun b a => frameStep (b, a)) (3, (List.replicate aW true, revOut)) =
          (8, (List.replicate aW true, false :: true :: revOut)) := by
        simp [frameStep, frameShouldShift, frameNext]
      rw [hs, h1 i.val (false :: true :: revOut)]
      simp [encInstr, encNat, mapInstr, List.append_assoc]
  | t i =>
      change ([true, true, false] ++ encNat i.val).foldl (fun b a => frameStep (b, a)) _ = _
      rw [List.foldl_append]
      have hs : ([true, true, false]).foldl (fun b a => frameStep (b, a))
            (3, (List.replicate aW true, revOut)) =
          (8, (List.replicate aW true, false :: true :: true :: revOut)) := by
        simp [frameStep, frameShouldShift, frameNext]
      rw [hs, h1 i.val (false :: true :: true :: revOut)]
      simp [encInstr, encNat, mapInstr, List.append_assoc]
  | x i =>
      change ([true, true, true, false] ++ encNat i.val).foldl (fun b a => frameStep (b, a)) _ = _
      rw [List.foldl_append]
      have hs : ([true, true, true, false]).foldl (fun b a => frameStep (b, a))
            (3, (List.replicate aW true, revOut)) =
          (8, (List.replicate aW true, false :: true :: true :: true :: revOut)) := by
        simp [frameStep, frameShouldShift, frameNext]
      rw [hs, h1 i.val (false :: true :: true :: true :: revOut)]
      simp [encInstr, encNat, mapInstr, List.append_assoc]
  | cnot i j hij =>
      change ([true, true, true, true, false] ++ encNat i.val ++ encNat j.val).foldl
        (fun b a => frameStep (b, a)) _ = _
      rw [List.foldl_append, List.foldl_append]
      have hs : ([true, true, true, true, false]).foldl (fun b a => frameStep (b, a))
            (3, (List.replicate aW true, revOut)) =
          (10, (List.replicate aW true, false :: true :: true :: true :: true :: revOut)) := by
        simp [frameStep, frameShouldShift, frameNext]
      rw [hs, h2 i.val (false :: true :: true :: true :: true :: revOut), h1 j.val _]
      simp [encInstr, encNat, mapInstr, List.append_assoc]

private lemma frame_foldl_layer {aW W : ℕ} (cl : List (Instr W)) (revOut : List Bool) :
    (cl.map encInstr).flatten.foldl (fun b a => frameStep (b, a))
        (3, (List.replicate aW true, revOut)) =
      (3, (List.replicate aW true,
        ((mapCirc (shiftEmb aW W (aW + W) le_rfl) cl).map encInstr).flatten.reverse ++ revOut)) := by
  induction cl generalizing revOut with
  | nil => simp [mapCirc]
  | cons ins cl ih =>
      simp only [List.map_cons, List.flatten_cons, List.foldl_append, mapCirc, List.reverse_append,
        List.append_assoc]
      rw [frame_foldl_instr ins revOut, ih]
      simp [mapCirc]

private lemma shiftFrameFun_correct {aW W : ℕ} (cl : List (Instr W)) :
    shiftFrameFun (encNat aW, encNat W ++ encLayer cl) =
      encNat (aW + W) ++ encLayer (mapCirc (shiftEmb aW W (aW + W) le_rfl) cl) := by
  simp only [shiftFrameFun, takeWhile_encNat, encLayer, encStr, mapCirc, List.length_map]
  have hw := frame_foldl_shift_encNat aW W 0 1 2 rfl rfl rfl rfl rfl rfl []
  have hlen := frame_foldl_copy_encNat aW cl.length 2 3 rfl rfl rfl ((encNat (aW + W)).reverse ++ [])
  have hlay := frame_foldl_layer (aW := aW) cl ((encNat cl.length).reverse ++ ((encNat (aW + W)).reverse ++ []))
  simp only [List.foldl_append]
  rw [hw, hlen, hlay]
  simp [mapCirc, List.append_assoc]

/-! ### Part 3: Circuit unitary and `Implements` preservation under left framing -/

private def splitQ (a b : ℕ) : Qubits (a + b) ≃ Qubits a × Qubits b where
  toFun z := (fun i => z (Fin.castAdd b i), fun j => z (Fin.natAdd a j))
  invFun p := Fin.append p.1 p.2
  left_inv z := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    rcases p with ⟨u, v⟩
    ext <;> simp

private def liftLeft (aW W : ℕ) (U : Matrix (Qubits W) (Qubits W) ℂ) :
    Matrix (Qubits (aW + W)) (Qubits (aW + W)) ℂ :=
  Matrix.of fun y z =>
    if (splitQ aW W y).1 = (splitQ aW W z).1
    then U (splitQ aW W y).2 (splitQ aW W z).2
    else 0

private lemma liftLeft_one (aW W : ℕ) : liftLeft aW W 1 = 1 := by
  ext y z
  simp only [liftLeft, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · have hsp : splitQ aW W y ≠ splitQ aW W z := fun h => hyz ((splitQ aW W).injective h)
    rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso; exact hsp (Prod.ext h1 h2)
    · rfl
    · rfl

private lemma liftLeft_mul (aW W : ℕ) (A B : Matrix (Qubits W) (Qubits W) ℂ) :
    liftLeft aW W (A * B) = liftLeft aW W A * liftLeft aW W B := by
  ext y z
  simp only [liftLeft, Matrix.of_apply, Matrix.mul_apply]
  rw [← (splitQ aW W).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  by_cases h1 : (splitQ aW W y).1 = (splitQ aW W z).1
  · rw [if_pos h1, h1]
    rw [Finset.sum_eq_single (splitQ aW W z).1]
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
    by_cases hx1 : (splitQ aW W y).1 = x
    · have hx2 : x ≠ (splitQ aW W z).1 := fun h => h1 (hx1.trans h)
      simp [hx2]
    · simp [hx1]

private lemma liftLeft_list_prod (aW W : ℕ) (ms : List (Matrix (Qubits W) (Qubits W) ℂ)) :
    (ms.map (liftLeft aW W)).prod = liftLeft aW W ms.prod := by
  induction ms with
  | nil => simp [liftLeft_one]
  | cons m ms ih => simp [ih, liftLeft_mul]

private lemma embedOp_shiftEmb {k aW W : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin W) :
    embedOp M (w.trans (shiftEmb aW W (aW + W) le_rfl)) = liftLeft aW W (embedOp M w) := by
  ext y z
  let e := shiftEmb aW W (aW + W) le_rfl
  simp only [embedOp, liftLeft, Matrix.of_apply]
  have hiff :
      (∀ a : Fin (aW + W), a ∉ Set.range (w.trans e) → y a = z a) ↔
      ((splitQ aW W y).1 = (splitQ aW W z).1 ∧
       ∀ b : Fin W, b ∉ Set.range w → (splitQ aW W y).2 b = (splitQ aW W z).2 b) := by
    constructor
    · intro h
      refine ⟨funext fun i => h (Fin.castAdd W i) ?_, fun b hb => h (Fin.natAdd aW b) ?_⟩
      · rintro ⟨x, hx⟩
        have hval := congrArg Fin.val hx
        rw [Fin.val_castAdd] at hval
        change aW + (w x).val = i.val at hval
        omega
      · rintro ⟨x, hx⟩
        apply hb
        refine ⟨x, Fin.ext ?_⟩
        have hval := congrArg Fin.val hx
        rw [Fin.val_natAdd] at hval
        change aW + (w x).val = aW + b.val at hval
        omega
    · rintro ⟨h1, h2⟩ a
      refine Fin.addCases (fun i _ => ?_) (fun b ha => ?_) a
      · exact congrFun h1 i
      · apply h2 b
        rintro ⟨x, hxb⟩
        apply ha
        refine ⟨x, Fin.ext ?_⟩
        have hxb' := congrArg Fin.val hxb
        rw [Fin.val_natAdd]
        change aW + (w x).val = aW + b.val
        omega
  have hcomp : y ∘ (w.trans e) = (splitQ aW W y).2 ∘ w := by
    funext x; rfl
  have hcompz : z ∘ (w.trans e) = (splitQ aW W z).2 ∘ w := by
    funext x; rfl
  by_cases hc : ∀ a : Fin (aW + W), a ∉ Set.range (w.trans e) → y a = z a
  · obtain ⟨h1, h2⟩ := hiff.mp hc
    rw [if_pos hc, if_pos h1, if_pos h2, hcomp, hcompz]
  · rw [if_neg hc]
    by_cases h1 : (splitQ aW W y).1 = (splitQ aW W z).1
    · rw [if_pos h1]
      have h2 : ¬ ∀ b : Fin W, b ∉ Set.range w → (splitQ aW W y).2 b = (splitQ aW W z).2 b :=
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

private lemma circUnitary_shiftCirc (aW W : ℕ) (cl : List (Instr W)) :
    circUnitary (mapCirc (shiftEmb aW W (aW + W) le_rfl) cl) =
      liftLeft aW W (circUnitary cl) := by
  simp only [circUnitary, Circuit.unitary, mapCirc, List.map_map]
  have hmap :
      List.map ((fun g : GateApp cliffordT (aW + W) => embedOp g.gate.mat g.wires) ∘
          instrApp ∘ mapInstr (shiftEmb aW W (aW + W) le_rfl)) cl =
      (List.map ((fun g : GateApp cliffordT W => embedOp g.gate.mat g.wires) ∘ instrApp) cl).map
        (liftLeft aW W) := by
    rw [List.map_map]
    refine List.map_congr_left fun ins _ => ?_
    simp only [Function.comp_apply, instrApp_mapInstr, embedOp_shiftEmb]
  rw [hmap, ← List.map_reverse, liftLeft_list_prod]

private lemma append_inj' {a b : ℕ} {u₁ u₂ : Qubits a} {v₁ v₂ : Qubits b}
    (h : Fin.append u₁ v₁ = Fin.append u₂ v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  refine ⟨funext fun i => ?_, funext fun j => ?_⟩
  · have hi := congrFun h (Fin.castAdd b i)
    simpa only [Fin.append_left] using hi
  · have hj := congrFun h (Fin.natAdd a j)
    simpa only [Fin.append_right] using hj

private lemma padTo_appendCode_left {A X : Type} {aW inW W : ℕ} (_hi : inW ≤ W)
    (ca : A → Qubits aW) (cin : X → Qubits inW) (a : A) (x : X) :
    padTo (aW + W) (appendCode ca cin (a, x)) = Fin.append (ca a) (padTo W (cin x)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hj : (Fin.castAdd W j : Fin (aW + W)).val < aW + inW := by
      simp only [Fin.val_castAdd]; omega
    simp only [padTo, appendCode, dif_pos hj, Fin.append_left]
    change Fin.append (ca a) (cin x) (Fin.castAdd inW j) = ca a j
    rw [Fin.append_left]
  · simp only [padTo, appendCode, Fin.val_natAdd, Fin.append_right]
    by_cases hj : j.val < inW
    · have h1 : aW + j.val < aW + inW := by omega
      rw [dif_pos h1, dif_pos hj]
      have hcast : (⟨aW + j.val, h1⟩ : Fin (aW + inW)) = Fin.natAdd aW ⟨j.val, hj⟩ := by
        ext; rfl
      rw [hcast, Fin.append_right]
    · have h1 : ¬ (aW + j.val < aW + inW) := by omega
      rw [dif_neg h1, dif_neg hj]

private lemma implements_frame {A X Y : Type} [Fintype A] [Fintype X] [Fintype Y] [DecidableEq A]
    {aW inW outW W : ℕ} {ca : A → Qubits aW} {cin : X → Qubits inW} {cout : Y → Qubits outW}
    {U : Matrix (Qubits W) (Qubits W) ℂ} {Φ : Matrix Y X ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hin : inW ≤ W) (hout : outW ≤ W) (hca : Function.Injective ca)
    (himp : Implements U (fun x => padTo W (cin x)) (fun y => padTo W (cout y)) Φ ε) :
    Implements (liftLeft aW W U)
      (fun p => padTo (aW + W) (appendCode ca cin p))
      (fun p => padTo (aW + W) (appendCode ca cout p))
      (frameMat Φ) ε := by
  intro ψ
  let ψa : A → EuclideanSpace ℂ X := fun a => WithLp.toLp 2 (fun x => ψ (a, x))
  let diff : EuclideanSpace ℂ (Qubits (aW + W)) :=
    act (liftLeft aW W U) (embedVec (fun p => padTo (aW + W) (appendCode ca cin p)) ψ) -
      embedVec (fun p => padTo (aW + W) (appendCode ca cout p))
        (WithLp.toLp 2 ((frameMat Φ).mulVec (WithLp.ofLp ψ)))
  let err : A → EuclideanSpace ℂ (Qubits W) := fun a =>
    act U (embedVec (fun x => padTo W (cin x)) (ψa a)) -
      embedVec (fun y => padTo W (cout y)) (WithLp.toLp 2 (Φ.mulVec (WithLp.ofLp (ψa a))))
  have hact_eq : ∀ (q1 : Qubits aW) (q2 : Qubits W),
      act (liftLeft aW W U) (embedVec (fun p => padTo (aW + W) (appendCode ca cin p)) ψ)
        (Fin.append q1 q2) =
      ∑ a : A, if ca a = q1 then act U (embedVec (fun x => padTo W (cin x)) (ψa a)) q2 else 0 := by
    intro q1 q2
    simp only [act, Matrix.mulVec, dotProduct, embedVec, WithLp.ofLp_toLp]
    rw [← (splitQ aW W).symm.sum_comp, Fintype.sum_prod_type]
    simp only [splitQ, Equiv.coe_fn_symm_mk]
    have hsplit : ∀ (z1 : Qubits aW) (z2 : Qubits W),
        (∑ x : A × X, if padTo (aW + W) (appendCode ca cin x) = Fin.append z1 z2 then ψ x else 0) =
        ∑ a : A, if ca a = z1 then ∑ x : X, if padTo W (cin x) = z2 then ψ (a, x) else 0 else 0 := by
      intro z1 z2
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : ca a = z1
      · rw [if_pos ha]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [padTo_appendCode_left hin, ha]
        by_cases hx : padTo W (cin x) = z2
        · simp [hx]
        · have hne : Fin.append z1 (padTo W (cin x)) ≠ Fin.append z1 z2 := by
            intro heq; exact hx (append_inj' heq).2
          simp [hx, hne]
      · rw [if_neg ha, Finset.sum_eq_zero]
        intro x _
        rw [padTo_appendCode_left hin]
        have hne : Fin.append (ca a) (padTo W (cin x)) ≠ Fin.append z1 z2 := by
          intro heq; exact ha (append_inj' heq).1
        rw [if_neg hne]
    simp only [liftLeft, Matrix.of_apply, splitQ, Equiv.coe_fn_mk, Fin.append_left, Fin.append_right]
    rw [Finset.sum_eq_single q1]
    · simp only [↓reduceIte]
      have hsum_y : ∀ y : Qubits W,
          U q2 y * (∑ x : A × X, if padTo (aW + W) (appendCode ca cin x) = Fin.append q1 y then ψ x else 0) =
          U q2 y * (∑ a : A, if ca a = q1 then ∑ x : X, if padTo W (cin x) = y then ψ (a, x) else 0 else 0) :=
        fun y => congrArg (U q2 y * ·) (hsplit q1 y)
      calc
        (∑ y : Qubits W, U q2 y * (∑ x : A × X,
            if padTo (aW + W) (appendCode ca cin x) = Fin.append q1 y then ψ x else 0))
            = ∑ y : Qubits W, U q2 y * (∑ a : A, if ca a = q1 then
                ∑ x : X, if padTo W (cin x) = y then ψ (a, x) else 0 else 0) :=
              Finset.sum_congr rfl fun y _ => hsum_y y
        _ = ∑ a : A, if ca a = q1 then ∑ y : Qubits W, U q2 y *
                ∑ x : X, if padTo W (cin x) = y then (ψa a) x else 0 else 0 := by
              simp only [Finset.mul_sum, mul_ite, mul_zero]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun a _ => ?_
              split_ifs with ha
              · rfl
              · simp
    · intro z1 _ hz1
      simp [Ne.symm hz1]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hout_eq : ∀ (q1 : Qubits aW) (q2 : Qubits W),
      embedVec (fun p => padTo (aW + W) (appendCode ca cout p))
        (WithLp.toLp 2 ((frameMat Φ).mulVec (WithLp.ofLp ψ))) (Fin.append q1 q2) =
      ∑ a : A, if ca a = q1 then
        embedVec (fun y => padTo W (cout y)) (WithLp.toLp 2 (Φ.mulVec (WithLp.ofLp (ψa a)))) q2
      else 0 := by
    intro q1 q2
    simp only [embedVec, WithLp.ofLp_toLp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : ca a = q1
    · rw [if_pos ha]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [padTo_appendCode_left hout, ha]
      by_cases hy : padTo W (cout y) = q2
      · rw [if_pos (by rw [hy]), if_pos hy]
        simp only [Matrix.mulVec, dotProduct, frameMat, Matrix.of_apply, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single a]
        · simp [ψa]
        · intro x _ hx; simp [Ne.symm hx]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · have hne : Fin.append q1 (padTo W (cout y)) ≠ Fin.append q1 q2 := by
          intro heq; exact hy (append_inj' heq).2
        rw [if_neg hne, if_neg hy]
    · rw [if_neg ha, Finset.sum_eq_zero]
      intro y _
      rw [padTo_appendCode_left hout]
      have hne : Fin.append (ca a) (padTo W (cout y)) ≠ Fin.append q1 q2 := by
        intro heq; exact ha (append_inj' heq).1
      rw [if_neg hne]
  have hdiff_eq : ∀ (q1 : Qubits aW) (q2 : Qubits W),
      diff (Fin.append q1 q2) = ∑ a : A, if ca a = q1 then err a q2 else 0 := by
    intro q1 q2
    change act (liftLeft aW W U) _ (Fin.append q1 q2) - embedVec _ _ (Fin.append q1 q2) = _
    rw [hact_eq, hout_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [err]
  have hnorm_sq : ‖diff‖ ^ 2 = ∑ a : A, ‖err a‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [← (splitQ aW W).symm.sum_comp, Fintype.sum_prod_type]
    simp only [splitQ, Equiv.coe_fn_symm_mk]
    have hq1 : ∀ q1 : Qubits aW,
        (∑ q2 : Qubits W, ‖diff (Fin.append q1 q2)‖ ^ 2) =
        ∑ a : A, if ca a = q1 then ‖err a‖ ^ 2 else 0 := by
      intro q1
      by_cases hex : ∃ a : A, ca a = q1
      · obtain ⟨a0, ha0⟩ := hex
        have huniq : ∀ a : A, ca a = q1 ↔ a = a0 := fun a =>
          ⟨fun h => hca (h.trans ha0.symm), fun h => h ▸ ha0⟩
        simp_rw [hdiff_eq, huniq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [EuclideanSpace.norm_sq_eq]
      · have hzero : ∀ a : A, ca a ≠ q1 := fun a h => hex ⟨a, h⟩
        have hsum0 : ∀ q2 : Qubits W, (∑ a : A, if ca a = q1 then err a q2 else 0) = 0 := fun q2 =>
          Finset.sum_eq_zero fun a _ => if_neg (hzero a)
        simp_rw [hdiff_eq, hsum0]
        simp [hzero]
    simp_rw [hq1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  have hpsi_sq : ‖ψ‖ ^ 2 = ∑ a : A, ‖ψa a‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
  have hsq_le : ‖diff‖ ^ 2 ≤ (ε * ‖ψ‖) ^ 2 := by
    rw [hnorm_sq, mul_pow, hpsi_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have ha := himp (ψa a)
    have hsq := sq_le_sq' (by linarith [norm_nonneg (err a)]) ha
    simpa [mul_pow] using hsq
  have hle : ‖diff‖ ≤ ε * ‖ψ‖ := by
    nlinarith [norm_nonneg diff, mul_nonneg hε (norm_nonneg ψ)]
  exact hle

theorem frame_proof
    {P : FieldData → Prop} {A X Y : FieldData → Type}
    [∀ D, Fintype (A D)] [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] [∀ D, DecidableEq (A D)]
    {aW inW outW : FieldData → ℕ}
    (ca : ∀ D, A D → Qubits (aW D))
    {cin : ∀ D, X D → Qubits (inW D)}
    {cout : ∀ D, Y D → Qubits (outW D)}
    {Φ : ∀ D, Matrix (Y D) (X D) ℂ}
    (h : UniformlyImplementsOn P cin cout Φ)
    (hca : ∀ D, P D → Function.Injective (ca D))
    (haw : ∃ fw : Str → Str, PolyTimeComputable fw ∧ ∀ D, P D → fw D.encData = encNat (aW D)) :
    UniformlyImplementsOn P
      (fun D => appendCode (ca D) (cin D))
      (fun D => appendCode (ca D) (cout D))
      (fun D => frameMat (Φ D)) := by
  obtain ⟨wires, circ, f, c, hf, hf_eq, hlen, himp⟩ := h
  obtain ⟨fw, hfw, hfw_eq⟩ := haw
  have hcomp_fw : PolyTimeComputable (fw ∘ extractData) := by
    obtain ⟨me⟩ := extractDataProgram.stock |> Nonempty.intro
    obtain ⟨mfw⟩ := hfw
    exact Turing.TM2ComputableInPolyTime.comp_of_polytime me mfw
  obtain ⟨mfan⟩ := polyTimeComputable_fanout hcomp_fw hf
  obtain ⟨mf'⟩ := Turing.TM2ComputableInPolyTime.comp_of_polytime mfan shiftFrameProgram.stock
  refine ⟨fun D k => aW D + wires D k,
    fun D k => mapCirc (shiftEmb (aW D) (wires D k) (aW D + wires D k) le_rfl) (circ D k),
    shiftFrameFun ∘ (fun x => (fw (extractData x), f x)), c, ⟨mf'⟩, ?_, ?_, ?_⟩
  · intro D hP k
    simp only [Function.comp_apply, extractData_encData, hfw_eq D hP, hf_eq D hP k]
    exact shiftFrameFun_correct (circ D k)
  · intro D hP k
    simpa only [mapCirc, List.length_map] using hlen D hP k
  · intro D hP k
    obtain ⟨hin, hout, hU⟩ := himp D hP k
    refine ⟨Nat.add_le_add_left hin _, Nat.add_le_add_left hout _, ?_⟩
    rw [circUnitary_shiftCirc]
    exact implements_frame (by positivity) hin hout (hca D hP) hU

end GL2QFT_Frame_Aux

theorem solution
    {P : GL2QFT.FieldData → Prop} {A X Y : GL2QFT.FieldData → Type}
    [∀ D, Fintype (A D)] [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] [∀ D, DecidableEq (A D)]
    {aW inW outW : GL2QFT.FieldData → ℕ}
    (ca : ∀ D, A D → QAlgorithms.Qubits (aW D))
    {cin : ∀ D, X D → QAlgorithms.Qubits (inW D)}
    {cout : ∀ D, Y D → QAlgorithms.Qubits (outW D)}
    {Φ : ∀ D, Matrix (Y D) (X D) ℂ}
    (h : GL2QFT.UniformlyImplementsOn P cin cout Φ)
    (hca : ∀ D, P D → Function.Injective (ca D))
    (haw : ∃ fw : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str,
      QAlgorithms.Complexity.PolyTimeComputable fw ∧
      ∀ D, P D → fw D.encData = QAlgorithms.Complexity.encNat (aW D)) :
    GL2QFT.UniformlyImplementsOn P
      (fun D => GL2QFT.Circuits.appendCode (ca D) (cin D))
      (fun D => GL2QFT.Circuits.appendCode (ca D) (cout D))
      (fun D => GL2QFT.Circuits.frameMat (Φ D)) :=
  GL2QFT_Frame_Aux.frame_proof ca h hca haw
