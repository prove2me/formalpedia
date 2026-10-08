-- Prove2me | solution 1 for FlowJobShop.SPT.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:09:19.274032+00:00
-- url     : https://prove2.me/submissions/531c99c1-bccb-47e8-a11b-d278b2bd8032

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core


namespace FlowJobShop.SPT

variable {m n : ℕ}

lemma ls_foldl_drop {β : Type*} (N : ℕ) (f : β → Fin N → β) (P : ℕ → β → Prop)
    (step : ∀ k (hk : k < N) x, P k x → P (k+1) (f x ⟨k, hk⟩)) :
    ∀ x, P 0 x → P N ((List.finRange N).foldl f x) := by
  have h : ∀ d k, k + d = N → ∀ x, P k x → P N (((List.finRange N).drop k).foldl f x) := by
    intro d
    induction d with
    | zero =>
      intro k hk x hx
      have hkN : k = N := by omega
      rw [List.drop_eq_nil_of_le (by simp; omega), List.foldl_nil, ← hkN]
      exact hx
    | succ d ih =>
      intro k hk x hx
      have hkN : k < N := by omega
      rw [List.drop_eq_getElem_cons (by simpa using hkN), List.foldl_cons]
      have e : (List.finRange N)[k]'(by simpa using hkN) = ⟨k, hkN⟩ := by simp
      rw [e]
      exact ih (k+1) (by omega) _ (step k hkN x hx)
  intro x hx
  simpa using h N 0 (by omega) x hx

/-- partial sum of the processing times of the first `k` tasks of job `j` -/
noncomputable def Sq (inst : Instance m n) (j : Fin n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, if h : i < inst.μ j then inst.p j ⟨i, h⟩ else 0

lemma Sq_succ (inst : Instance m n) (j : Fin n) (k : ℕ) (hk : k < inst.μ j) :
    Sq inst j (k+1) = Sq inst j k + inst.p j ⟨k, hk⟩ := by
  unfold Sq
  rw [Finset.sum_range_succ, dif_pos hk]

lemma Sq_full (inst : Instance m n) (j : Fin n) : Sq inst j (inst.μ j) = inst.jobLength j := by
  unfold Sq Instance.jobLength
  rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < inst.μ j then inst.p j ⟨i, h⟩ else 0)]
  apply Finset.sum_congr rfl
  intro i _
  simp [i.isLt]

structure PInv (inst : Instance m n) (j : Fin n) (B : ℝ) (st0 : ListState inst)
    (Q₀ : Set inst.Op) (k : ℕ) (st : ListState inst) (c : ℝ) : Prop where
  same : ∀ o : inst.Op, o.1 ≠ j → st.start o = st0.start o
  nonneg : ∀ o : inst.Op, (o ∈ Q₀ ∨ (o.1 = j ∧ o.2.val < k)) → 0 ≤ st.start o
  cover : ∀ o : inst.Op, (o ∈ Q₀ ∨ (o.1 = j ∧ o.2.val < k)) → 0 < inst.proc o →
    st.start o + inst.proc o ≤ st.avail (inst.mach o)
  disj : ∀ o o' : inst.Op, (o ∈ Q₀ ∨ (o.1 = j ∧ o.2.val < k)) →
    (o' ∈ Q₀ ∨ (o'.1 = j ∧ o'.2.val < k)) → o ≠ o' → inst.mach o = inst.mach o' →
    0 < inst.proc o → 0 < inst.proc o' →
    st.start o + inst.proc o ≤ st.start o' ∨ st.start o' + inst.proc o' ≤ st.start o
  prec : ∀ i i' : Fin (inst.μ j), i.val + 1 = i'.val → i'.val < k →
    st.start ⟨j, i⟩ + inst.p j i ≤ st.start ⟨j, i'⟩
  cval : ∀ i : Fin (inst.μ j), i.val + 1 = k → c = st.start ⟨j, i⟩ + inst.p j i
  c0 : k = 0 → c = 0
  c_nonneg : 0 ≤ c
  av_nonneg : ∀ t, 0 ≤ st.avail t
  c_le : c ≤ B + Sq inst j k
  av_le : ∀ t, st.avail t ≤ B + Sq inst j k
  fin_le : ∀ i : Fin (inst.μ j), i.val < k → st.start ⟨j, i⟩ + inst.p j i ≤ B + Sq inst j k

lemma pinv_step (inst : Instance m n) (j : Fin n) (B : ℝ) (st0 : ListState inst)
    (Q₀ : Set inst.Op) (hQ₀ : ∀ o ∈ Q₀, o.1 ≠ j) (k : ℕ) (hk : k < inst.μ j)
    (x : ListState inst × ℝ) (h : PInv inst j B st0 Q₀ k x.1 x.2) :
    PInv inst j B st0 Q₀ (k+1) (placeTask inst j x ⟨k, hk⟩).1 (placeTask inst j x ⟨k, hk⟩).2 := by
  obtain ⟨st, c⟩ := x
  simp only at h
  set i₀ : Fin (inst.μ j) := ⟨k, hk⟩ with hi₀
  set o₀ : inst.Op := ⟨j, i₀⟩ with ho₀
  have hp0 : 0 ≤ inst.p j i₀ := inst.p_nonneg _ _
  have ho₀Q : ¬ (o₀ ∈ Q₀ ∨ (o₀.1 = j ∧ o₀.2.val < k)) := by
    rintro (h1 | h1)
    · exact hQ₀ _ h1 rfl
    · exact absurd h1.2 (by have h2 : o₀.2.val = k := rfl; omega)
  obtain ⟨b, hbdef⟩ : ∃ b, b = if inst.p j i₀ = 0 then c else max c (st.avail (inst.π j i₀)) :=
    ⟨_, rfl⟩
  have hbc : c ≤ b := by rw [hbdef]; split_ifs <;> simp
  have hbav : inst.p j i₀ ≠ 0 → st.avail (inst.π j i₀) ≤ b := by
    intro hne; rw [hbdef, if_neg hne]; exact le_max_right _ _
  have hbB : b ≤ B + Sq inst j k := by
    rw [hbdef]; split_ifs
    · exact h.c_le
    · exact max_le h.c_le (h.av_le _)
  have hb0 : 0 ≤ b := h.c_nonneg.trans hbc
  have hpl : placeTask inst j (st, c) i₀ =
      (⟨if inst.p j i₀ = 0 then st.avail else
          Function.update st.avail (inst.π j i₀) (b + inst.p j i₀),
        Function.update st.start o₀ b⟩, b + inst.p j i₀) := by
    simp only [placeTask]
    rw [hbdef]
  have hS := Sq_succ inst j k hk
  have hmem : ∀ o : inst.Op, (o ∈ Q₀ ∨ (o.1 = j ∧ o.2.val < k+1)) ↔
      ((o ∈ Q₀ ∨ (o.1 = j ∧ o.2.val < k)) ∨ o = o₀) := by
    intro o
    obtain ⟨j', i'⟩ := o
    simp only [ho₀, hi₀, Sigma.mk.injEq]
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl (Or.inl h1)
      · subst h1
        by_cases hlt : i'.val < k
        · exact Or.inl (Or.inr ⟨rfl, hlt⟩)
        · refine Or.inr ⟨rfl, ?_⟩
          rw [heq_iff_eq]
          ext; simp only at h2 ⊢; omega
    · rintro ((h1 | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, by omega⟩
      · subst h1
        rw [heq_iff_eq] at h2
        subst h2
        exact Or.inr ⟨rfl, by simp⟩
  have hne : ∀ o : inst.Op, (o ∈ Q₀ ∨ (o.1 = j ∧ o.2.val < k)) → o ≠ o₀ := by
    intro o ho he; subst he; exact ho₀Q ho
  have hOp : ∀ i : Fin (inst.μ j), (⟨j, i⟩ : inst.Op) = o₀ ↔ i.val = k := by
    intro i
    constructor
    · intro he
      exact congrArg (fun o : inst.Op => o.2.val) he
    · intro h
      show (⟨j, i⟩ : inst.Op) = ⟨j, i₀⟩
      congr 1
      ext
      exact h
  have hst : ∀ o : inst.Op, o ≠ o₀ → Function.update st.start o₀ b o = st.start o :=
    fun o ho => Function.update_of_ne ho _ _
  have hst0 : Function.update st.start o₀ b o₀ = b := Function.update_self _ _ _
  rw [hpl]
  simp only
  have hmach : inst.mach o₀ = inst.π j i₀ := rfl
  have hproc : inst.proc o₀ = inst.p j i₀ := rfl
  constructor
  all_goals try dsimp only
  · intro o ho
    have : o ≠ o₀ := fun he => ho (by rw [he])
    rw [hst o this]
    exact h.same o ho
  · intro o ho
    rcases (hmem o).1 ho with ho | rfl
    · rw [hst o (hne o ho)]; exact h.nonneg o ho
    · rw [hst0]; exact hb0
  · intro o ho hpos
    rcases (hmem o).1 ho with ho | rfl
    · have hn := hne o ho
      rw [hst o hn]
      have := h.cover o ho hpos
      by_cases hp : inst.p j i₀ = 0
      · rw [if_pos hp]; exact this
      · rw [if_neg hp]
        by_cases hm : inst.mach o = inst.π j i₀
        · have h1 := hbav hp
          have h2 := this
          rw [hm] at h2
          rw [hm, Function.update_self]
          linarith [hp0]
        · rw [Function.update_of_ne hm]; exact this
    · rw [hst0]
      have hp : inst.p j i₀ ≠ 0 := by
        intro h0; rw [hproc, h0] at hpos; exact lt_irrefl _ hpos
      rw [if_neg hp, hmach, Function.update_self, hproc]
  · intro o o' ho ho' hoo hm hpos hpos'
    rcases (hmem o).1 ho with ho | rfl <;> rcases (hmem o').1 ho' with ho' | rfl
    · rw [hst o (hne o ho), hst o' (hne o' ho')]
      exact h.disj o o' ho ho' hoo hm hpos hpos'
    · have hp : inst.p j i₀ ≠ 0 := by
        intro h0; rw [hproc, h0] at hpos'; exact lt_irrefl _ hpos'
      left
      rw [hst o (hne o ho), hst0]
      have h1 := h.cover o ho hpos
      have h2 := hbav hp
      rw [hm, hmach] at h1
      linarith
    · have hp : inst.p j i₀ ≠ 0 := by
        intro h0; rw [hproc, h0] at hpos; exact lt_irrefl _ hpos
      right
      rw [hst o' (hne o' ho'), hst0]
      have h1 := h.cover o' ho' hpos'
      have h2 := hbav hp
      rw [← hm, hmach] at h1
      linarith
    · exact absurd rfl hoo
  · intro i i' hii hi'
    have hi'k : i'.val < k + 1 := hi'
    by_cases hlt : i'.val < k
    · have e1 : (⟨j, i⟩ : inst.Op) ≠ o₀ := by
        intro he; have := (hOp i).1 he; omega
      have e2 : (⟨j, i'⟩ : inst.Op) ≠ o₀ := by
        intro he; have := (hOp i').1 he; omega
      rw [hst _ e1, hst _ e2]
      exact h.prec i i' hii hlt
    · have hik : i'.val = k := by omega
      have e1 : (⟨j, i⟩ : inst.Op) ≠ o₀ := by
        intro he; have := (hOp i).1 he; omega
      have e2 : (⟨j, i'⟩ : inst.Op) = o₀ := (hOp i').2 hik
      rw [hst _ e1, e2, hst0]
      have := h.cval i (by omega)
      linarith
  · intro i hi
    have : i = i₀ := by ext; simp only [hi₀]; omega
    subst this
    rw [hst0]
  · intro h0; omega
  · linarith
  · intro t
    by_cases hp : inst.p j i₀ = 0
    · rw [if_pos hp]; exact h.av_nonneg t
    · rw [if_neg hp]
      by_cases ht : t = inst.π j i₀
      · rw [ht, Function.update_self]; linarith
      · rw [Function.update_of_ne ht]; exact h.av_nonneg t
  · rw [hS]; linarith
  · intro t
    by_cases hp : inst.p j i₀ = 0
    · rw [if_pos hp]; have := h.av_le t; rw [hS]; linarith
    · rw [if_neg hp]
      by_cases ht : t = inst.π j i₀
      · rw [ht, Function.update_self, hS]; linarith
      · rw [Function.update_of_ne ht, hS]; have := h.av_le t; linarith
  · intro i hi
    by_cases hlt : i.val < k
    · have e1 : (⟨j, i⟩ : inst.Op) ≠ o₀ := by
        intro he; have := (hOp i).1 he; omega
      rw [hst _ e1, hS]
      have := h.fin_le i hlt
      linarith
    · have : i = i₀ := by ext; simp only [hi₀]; omega
      subst this
      rw [hst0, hS]; linarith


lemma placeJob_inv (inst : Instance m n) (j : Fin n) (B : ℝ) (hB : 0 ≤ B) (st : ListState inst)
    (Q₀ : Set inst.Op) (hQ₀ : ∀ o ∈ Q₀, o.1 ≠ j)
    (hnn : ∀ o ∈ Q₀, 0 ≤ st.start o)
    (hcov : ∀ o ∈ Q₀, 0 < inst.proc o → st.start o + inst.proc o ≤ st.avail (inst.mach o))
    (hdis : ∀ o ∈ Q₀, ∀ o' ∈ Q₀, o ≠ o' → inst.mach o = inst.mach o' →
      0 < inst.proc o → 0 < inst.proc o' →
      st.start o + inst.proc o ≤ st.start o' ∨ st.start o' + inst.proc o' ≤ st.start o)
    (hav0 : ∀ t, 0 ≤ st.avail t) (havB : ∀ t, st.avail t ≤ B) :
    ∃ c, PInv inst j B st Q₀ (inst.μ j) (placeJob inst st j) c := by
  have h := ls_foldl_drop (inst.μ j) (placeTask inst j)
    (fun k x => PInv inst j B st Q₀ k x.1 x.2)
    (fun k hk x hx => pinv_step inst j B st Q₀ hQ₀ k hk x hx) (st, 0) (by
      have hS0 : Sq inst j 0 = 0 := by simp [Sq]
      show PInv inst j B st Q₀ 0 (st, 0).1 (st, 0).2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro o _; rfl
      · rintro o (ho | ⟨_, h2⟩)
        · exact hnn o ho
        · exact absurd h2 (by omega)
      · rintro o (ho | ⟨_, h2⟩) hp
        · exact hcov o ho hp
        · exact absurd h2 (by omega)
      · rintro o o' (ho | ⟨_, h2⟩) (ho' | ⟨_, h2'⟩) hne hm hp hp'
        · exact hdis o ho o' ho' hne hm hp hp'
        · exact absurd h2' (by omega)
        · exact absurd h2 (by omega)
        · exact absurd h2 (by omega)
      · intro i i' _ h; exact absurd h (by omega)
      · intro i h; exact absurd h (by omega)
      · intro _; rfl
      · exact le_rfl
      · exact hav0
      · show (0:ℝ) ≤ _
        rw [hS0]; linarith
      · intro t; show st.avail t ≤ _
        rw [hS0]; linarith [havB t]
      · intro i h; exact absurd h (by omega))
  exact ⟨_, h⟩

/-- the prefix sums of job lengths in the order `σ` -/
noncomputable def Tq (inst : Instance m n) (σ : Fin n ≃ Fin n) (k : ℕ) : ℝ :=
  ∑ q ∈ Finset.range k, if h : q < n then inst.jobLength (σ ⟨q, h⟩) else 0

lemma Tq_succ (inst : Instance m n) (σ : Fin n ≃ Fin n) (k : ℕ) (hk : k < n) :
    Tq inst σ (k+1) = Tq inst σ k + inst.jobLength (σ ⟨k, hk⟩) := by
  unfold Tq
  rw [Finset.sum_range_succ, dif_pos hk]

lemma Tq_nonneg (inst : Instance m n) (σ : Fin n ≃ Fin n) (k : ℕ) : 0 ≤ Tq inst σ k := by
  unfold Tq
  apply Finset.sum_nonneg
  intro q _
  split_ifs
  · exact Finset.sum_nonneg (fun i _ => inst.p_nonneg _ _)
  · exact le_rfl

lemma Tq_Iic (inst : Instance m n) (σ : Fin n ≃ Fin n) (k : Fin n) :
    Tq inst σ (k.val + 1) = ∑ j ∈ Finset.Iic k, inst.jobLength (σ j) := by
  unfold Tq
  symm
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_Iic] at hj
    simp only [Finset.mem_range]
    have : j.val ≤ k.val := hj
    omega
  · intro a _ b _ h; exact Fin.ext h
  · intro i hi
    simp only [Finset.mem_range] at hi
    refine ⟨⟨i, by have := k.isLt; omega⟩, ?_, rfl⟩
    simp only [Finset.mem_Iic]
    show i ≤ k.val
    omega
  · intro j _
    simp [j.isLt]

/-- jobs placed so far -/
def Qg (inst : Instance m n) (σ : Fin n ≃ Fin n) (k : ℕ) : Set inst.Op :=
  {o | ∃ q : Fin n, q.val < k ∧ o.1 = σ q}

structure GInv (inst : Instance m n) (σ : Fin n ≃ Fin n) (k : ℕ) (st : ListState inst) : Prop where
  nonneg : ∀ o ∈ Qg inst σ k, 0 ≤ st.start o
  cover : ∀ o ∈ Qg inst σ k, 0 < inst.proc o → st.start o + inst.proc o ≤ st.avail (inst.mach o)
  disj : ∀ o ∈ Qg inst σ k, ∀ o' ∈ Qg inst σ k, o ≠ o' → inst.mach o = inst.mach o' →
    0 < inst.proc o → 0 < inst.proc o' →
    st.start o + inst.proc o ≤ st.start o' ∨ st.start o' + inst.proc o' ≤ st.start o
  prec : ∀ q : Fin n, q.val < k → ∀ i i' : Fin (inst.μ (σ q)), i.val + 1 = i'.val →
    st.start ⟨σ q, i⟩ + inst.p (σ q) i ≤ st.start ⟨σ q, i'⟩
  av_nonneg : ∀ t, 0 ≤ st.avail t
  av_le : ∀ t, st.avail t ≤ Tq inst σ k
  fin_le : ∀ q : Fin n, q.val < k → ∀ i : Fin (inst.μ (σ q)),
    st.start ⟨σ q, i⟩ + inst.p (σ q) i ≤ Tq inst σ (q.val + 1)

lemma ginv_step (inst : Instance m n) (σ : Fin n ≃ Fin n) (k : ℕ) (hk : k < n)
    (st : ListState inst) (h : GInv inst σ k st) :
    GInv inst σ (k+1) (placeJob inst st (σ ⟨k, hk⟩)) := by
  have hQ₀ : ∀ o ∈ Qg inst σ k, o.1 ≠ σ ⟨k, hk⟩ := by
    rintro o ⟨q, hq, hqo⟩ he
    rw [hqo] at he
    have := σ.injective he
    have : q.val = k := congrArg Fin.val this
    omega
  obtain ⟨c, P⟩ := placeJob_inv inst (σ ⟨k, hk⟩) (Tq inst σ k) (Tq_nonneg inst σ k) st
    (Qg inst σ k) hQ₀ h.nonneg h.cover h.disj h.av_nonneg h.av_le
  have hSq := Sq_full inst (σ ⟨k, hk⟩)
  have hT := Tq_succ inst σ k hk
  have hmem : ∀ o : inst.Op, o ∈ Qg inst σ (k+1) ↔
      (o ∈ Qg inst σ k ∨ (o.1 = σ ⟨k, hk⟩ ∧ o.2.val < inst.μ (σ ⟨k, hk⟩))) := by
    intro o
    obtain ⟨j', i'⟩ := o
    constructor
    · rintro ⟨q, hq, hqo⟩
      by_cases hlt : q.val < k
      · exact Or.inl ⟨q, hlt, hqo⟩
      · have : q = ⟨k, hk⟩ := Fin.ext (by simp only; omega)
        subst this
        have hqo' : j' = σ ⟨k, hk⟩ := hqo
        subst hqo'
        exact Or.inr ⟨rfl, i'.isLt⟩
    · rintro (⟨q, hq, hqo⟩ | ⟨h1, h2⟩)
      · exact ⟨q, by omega, hqo⟩
      · exact ⟨⟨k, hk⟩, by simp, h1⟩
  have hne : ∀ q : Fin n, q.val < k → σ q ≠ σ ⟨k, hk⟩ := by
    intro q hq he
    have := congrArg Fin.val (σ.injective he)
    simp only at this
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho; exact P.nonneg o ((hmem o).1 ho)
  · intro o ho hp; exact P.cover o ((hmem o).1 ho) hp
  · intro o ho o' ho' hne' hm hp hp'
    exact P.disj o o' ((hmem o).1 ho) ((hmem o').1 ho') hne' hm hp hp'
  · intro q hq i i' hii
    by_cases hlt : q.val < k
    · rw [P.same ⟨σ q, i⟩ (hne q hlt), P.same ⟨σ q, i'⟩ (hne q hlt)]
      exact h.prec q hlt i i' hii
    · have : q = ⟨k, hk⟩ := Fin.ext (by simp only; omega)
      subst this
      exact P.prec i i' hii i'.isLt
  · exact P.av_nonneg
  · intro t
    have := P.av_le t
    rw [hSq, ← hT] at this
    exact this
  · intro q hq i
    by_cases hlt : q.val < k
    · rw [P.same ⟨σ q, i⟩ (hne q hlt)]
      exact h.fin_le q hlt i
    · have : q = ⟨k, hk⟩ := Fin.ext (by simp only; omega)
      subst this
      have := P.fin_le i i.isLt
      rw [hSq, ← hT] at this
      exact this


lemma ginv_all (inst : Instance m n) (σ : Fin n ≃ Fin n) :
    GInv inst σ n ((List.finRange n).foldl (fun st k => placeJob inst st (σ k))
      (⟨fun _ => 0, fun _ => 0⟩ : ListState inst)) := by
  apply ls_foldl_drop n (fun st k => placeJob inst st (σ k)) (fun k st => GInv inst σ k st)
    (fun k hk x hx => ginv_step inst σ k hk x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro o ⟨q, hq, _⟩; exact absurd hq (by omega)
  · rintro o ⟨q, hq, _⟩; exact absurd hq (by omega)
  · rintro o ⟨q, hq, _⟩; exact absurd hq (by omega)
  · intro q hq; exact absurd hq (by omega)
  · intro t; exact le_rfl
  · intro t; exact Tq_nonneg inst σ 0
  · intro q hq; exact absurd hq (by omega)

theorem lsf_core {m n : ℕ} (inst : Instance m n) (σ : Fin n ≃ Fin n) :
    IsPaperFeasibleSchedule inst (listSchedule inst σ) := by
  have G := ginv_all inst σ
  have hall : ∀ o : inst.Op, o ∈ Qg inst σ n := fun o => ⟨σ.symm o.1, (σ.symm o.1).isLt, by simp⟩
  unfold listSchedule
  refine ⟨fun o => G.nonneg o (hall o), ?_, ?_⟩
  · intro j i i' h
    obtain ⟨q, rfl⟩ := σ.surjective j
    exact G.prec q q.isLt i i' h
  · intro o o' hne hm hp hp'
    exact G.disj o (hall o) o' (hall o') hne hm hp hp'

theorem lsfin_core {m n : ℕ} (inst : Instance m n) (σ : Fin n ≃ Fin n) (k : Fin n) :
    finishTime inst (listSchedule inst σ) (σ k) ≤
      ∑ j ∈ Finset.Iic k, inst.jobLength (σ j) := by
  have G := ginv_all inst σ
  rw [← Tq_Iic]
  unfold finishTime listSchedule
  rw [Finset.fold_max_le]
  exact ⟨Tq_nonneg inst σ _, fun i _ => G.fin_le k k.isLt i⟩


open MeasureTheory

lemma wlb_disjoint_sum {ι : Type*} (O : Finset ι) (s p : ι → ℝ) (F : ℝ) (hF0 : 0 ≤ F)
    (hp : ∀ o ∈ O, 0 < p o) (h0 : ∀ o ∈ O, 0 ≤ s o) (hF : ∀ o ∈ O, s o + p o ≤ F)
    (hd : ∀ o ∈ O, ∀ o' ∈ O, o ≠ o' → s o + p o ≤ s o' ∨ s o' + p o' ≤ s o) :
    ∑ o ∈ O, p o ≤ F := by
  classical
  have hdis : (↑O : Set ι).PairwiseDisjoint (fun o => Set.Ico (s o) (s o + p o)) := by
    intro o ho o' ho' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Ico] at hx hx'
    rcases hd o ho o' ho' hne with h | h <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  have h1 : volume (⋃ o ∈ O, Set.Ico (s o) (s o + p o)) = ∑ o ∈ O, ENNReal.ofReal (p o) := by
    rw [measure_biUnion_finset hdis (fun o _ => measurableSet_Ico)]
    apply Finset.sum_congr rfl
    intro o _
    simp
  have h2 : volume (⋃ o ∈ O, Set.Ico (s o) (s o + p o)) ≤ volume (Set.Icc (0:ℝ) F) := by
    apply measure_mono
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ico] at hx
    obtain ⟨o, ho, h1, h2⟩ := hx
    simp only [Set.mem_Icc]
    constructor
    · linarith [h0 o ho]
    · linarith [hF o ho, hp o ho]
  rw [h1, Real.volume_Icc, sub_zero] at h2
  rw [← ENNReal.ofReal_sum_of_nonneg (fun o ho => (hp o ho).le)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hF0).1 h2


lemma fin_ge {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ) (j : Fin n) (i : Fin (inst.μ j)) :
    s ⟨j, i⟩ + inst.p j i ≤ finishTime inst s j := by
  unfold finishTime
  rw [Finset.le_fold_max]
  exact Or.inr ⟨i, Finset.mem_univ _, le_rfl⟩

lemma fin_nonneg {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ) (j : Fin n) :
    0 ≤ finishTime inst s j := by
  unfold finishTime
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

theorem wlb_core {m n : ℕ} (inst : Instance m n) (τ : inst.Op → ℝ)
    (hτ : IsPaperFeasibleSchedule inst τ) (ρ : Fin n ≃ Fin n)
    (hρ : Monotone fun k => finishTime inst τ (ρ k)) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, inst.jobLength (ρ j) ≤ (m : ℝ) * finishTime inst τ (ρ k) := by
  classical
  set F := finishTime inst τ (ρ k) with hFdef
  have hF0 : 0 ≤ F := fin_nonneg inst τ _
  set J : Finset (Fin n) := (Finset.Iic k).map ρ.toEmbedding with hJ
  have e1 : ∑ j ∈ Finset.Iic k, inst.jobLength (ρ j) = ∑ j ∈ J, inst.jobLength j := by
    rw [hJ, Finset.sum_map]; rfl
  set O : Finset inst.Op := J.sigma (fun j => (Finset.univ : Finset (Fin (inst.μ j)))) with hO
  have e2 : ∑ j ∈ J, inst.jobLength j = ∑ o ∈ O, inst.proc o := by
    rw [hO, Finset.sum_sigma]; rfl
  have e3 : ∑ o ∈ O, inst.proc o = ∑ t : Fin m, ∑ o ∈ O with inst.mach o = t, inst.proc o :=
    (Finset.sum_fiberwise O inst.mach inst.proc).symm
  have hmem : ∀ o ∈ O, o.1 ∈ J := by
    intro o ho; rw [hO, Finset.mem_sigma] at ho; exact ho.1
  have hle : ∀ o ∈ O, τ o + inst.proc o ≤ F := by
    intro o ho
    have h1 := hmem o ho
    rw [hJ, Finset.mem_map] at h1
    obtain ⟨j', hj', hj'e⟩ := h1
    have : finishTime inst τ o.1 ≤ F := by
      rw [← hj'e]
      exact hρ (by simpa using hj')
    exact le_trans (fin_ge inst τ o.1 o.2) this
  have e4 : ∀ t : Fin m, ∑ o ∈ O with inst.mach o = t, inst.proc o ≤ F := by
    intro t
    rw [← Finset.sum_filter_of_ne (p := fun o => 0 < inst.proc o)]
    · apply wlb_disjoint_sum _ τ inst.proc F hF0
      · intro o ho; simp at ho; exact ho.2
      · intro o _; exact hτ.start_nonneg o
      · intro o ho; simp only [Finset.mem_filter] at ho; exact hle o ho.1.1
      · intro o ho o' ho' hne
        simp only [Finset.mem_filter] at ho ho'
        exact hτ.machine_disjoint o o' hne (ho.1.2.trans ho'.1.2.symm) ho.2 ho'.2
    · intro o ho hne
      have : 0 ≤ inst.proc o := inst.p_nonneg _ _
      exact lt_of_le_of_ne this (Ne.symm hne)
  rw [e1, e2, e3]
  calc _ ≤ ∑ t : Fin m, F := Finset.sum_le_sum (fun t _ => e4 t)
    _ = _ := by simp


theorem spl_core {n : ℕ} (L : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hσ : Monotone fun k => L (σ k)) (ρ : Fin n ≃ Fin n) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, L (σ j) ≤ ∑ j ∈ Finset.Iic k, L (ρ j) := by
  classical
  set a : Fin n → ℝ := fun i => L (σ i) with ha
  have hL : ∀ x, L x = a (σ.symm x) := by intro x; simp [ha]
  have h2 : ∑ j ∈ Finset.Iic k, L (ρ j) = ∑ j ∈ (Finset.Iic k).map (ρ.trans σ.symm).toEmbedding, a j := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    simp [hL]
  rw [h2]
  set I := Finset.Iic k with hI
  set T := I.map (ρ.trans σ.symm).toEmbedding with hT
  have hc : T.card = I.card := by simp [hT]
  have hc2 : (T \ I).card = (I \ T).card := Finset.card_sdiff_comm hc
  have e1 : ∑ j ∈ T, a j = ∑ j ∈ T \ I, a j + ∑ j ∈ T ∩ I, a j := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T I), Finset.sdiff_union_inter]
  have e2 : ∑ j ∈ I, a j = ∑ j ∈ I \ T, a j + ∑ j ∈ T ∩ I, a j := by
    rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter I T), Finset.sdiff_union_inter]
  have b1 : ∑ j ∈ I \ T, a j ≤ (I \ T).card • a k := by
    apply Finset.sum_le_card_nsmul
    intro x hx
    have : x ≤ k := by simpa [hI] using (Finset.mem_sdiff.1 hx).1
    exact hσ this
  have b2 : (T \ I).card • a k ≤ ∑ j ∈ T \ I, a j := by
    apply Finset.card_nsmul_le_sum
    intro x hx
    have : ¬ x ≤ k := by simpa [hI] using (Finset.mem_sdiff.1 hx).2
    exact hσ (le_of_lt (not_le.1 this))
  rw [hc2] at b2
  linarith


theorem mlb_core {m n : ℕ} (inst : Instance m n) (σ : Fin n ≃ Fin n)
    (hσ : IsSPTOrder inst σ) (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    (∑ k : Fin n, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j)) / n ≤
      (m : ℝ) * meanFlowTime inst τ := by
  classical
  set ρ := Tuple.sort (fun j => finishTime inst τ j) with hρ
  have hmono : Monotone fun k => finishTime inst τ (ρ k) := Tuple.monotone_sort (fun j => finishTime inst τ j)
  have key : ∀ k, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j) ≤ (m : ℝ) * finishTime inst τ (ρ k) :=
    fun k => (spl_core inst.jobLength σ hσ ρ k).trans (wlb_core inst τ hτ ρ hmono k)
  have h1 : (∑ k : Fin n, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j)) ≤ (m : ℝ) * ∑ j, finishTime inst τ j := by
    calc _ ≤ ∑ k : Fin n, (m : ℝ) * finishTime inst τ (ρ k) := Finset.sum_le_sum (fun k _ => key k)
      _ = (m : ℝ) * ∑ k : Fin n, finishTime inst τ (ρ k) := by rw [Finset.mul_sum]
      _ = _ := by rw [Equiv.sum_comp ρ (fun j => finishTime inst τ j)]
  unfold meanFlowTime
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg n)


theorem l9_core {m n : ℕ} (inst : Instance m n)
    (σ : Fin n ≃ Fin n) (hσ : IsSPTOrder inst σ)
    (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    meanFlowTime inst (listSchedule inst σ) ≤ (m : ℝ) * meanFlowTime inst τ := by
  have h1 := mlb_core inst σ hσ τ hτ
  refine le_trans ?_ h1
  unfold meanFlowTime
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc ∑ j, finishTime inst (listSchedule inst σ) j
      = ∑ k, finishTime inst (listSchedule inst σ) (σ k) := (Equiv.sum_comp σ _).symm
    _ ≤ _ := Finset.sum_le_sum (fun k _ => lsfin_core inst σ k)

end FlowJobShop.SPT

open FlowJobShop.SPT


theorem solution {m n : ℕ} (inst : Instance m n) (hm : 0 < m)
    (σ : Fin n ≃ Fin n) (hσ : IsSPTOrder inst σ)
    (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    meanFlowTime inst (listSchedule inst σ) ≤ (m : ℝ) * meanFlowTime inst τ := by
  exact l9_core inst σ hσ τ hτ
