-- Prove2me | solution 1 for BNCovPack.SetCover.lemma_5_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:37:12.317358+00:00
-- url     : https://prove2.me/submissions/662849c7-c727-424e-acf3-fea3fd6f5fe9

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_BNCovPack_SetCover_Potential



namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

lemma pot_prod_clamp {ι : Type*} [DecidableEq ι] (S : Finset ι) (f f' : ι → ℝ) (v : ℝ)
    (h0 : ∀ i ∈ S, 0 ≤ f i) (hff : ∀ i ∈ S, f i ≤ f' i) (hf1 : ∀ i ∈ S, f' i ≤ 1)
    (hv' : ∀ i ∈ S, f' i ≤ v * f i) :
    1 - ∏ i ∈ S, (1 - f' i) ≤ v * (1 - ∏ i ∈ S, (1 - f i)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hff i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hv' i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hA : 0 ≤ ∏ i ∈ S, (1 - f i) :=
      Finset.prod_nonneg (fun i hi => by
        have := hff i (Finset.mem_insert_of_mem hi)
        have := hf1 i (Finset.mem_insert_of_mem hi)
        linarith)
    have hA' : 0 ≤ ∏ i ∈ S, (1 - f' i) :=
      Finset.prod_nonneg (fun i hi => by
        have := hf1 i (Finset.mem_insert_of_mem hi)
        linarith)
    have hle : ∏ i ∈ S, (1 - f' i) ≤ ∏ i ∈ S, (1 - f i) :=
      Finset.prod_le_prod (fun i hi => by
        have := hf1 i (Finset.mem_insert_of_mem hi)
        linarith) (fun i hi => by
        have := hff i (Finset.mem_insert_of_mem hi)
        linarith)
    have ha0 := h0 a (Finset.mem_insert_self a S)
    have haff := hff a (Finset.mem_insert_self a S)
    have hav := hv' a (Finset.mem_insert_self a S)
    have h1 : f' a * ∏ i ∈ S, (1 - f' i) ≤ v * f a * ∏ i ∈ S, (1 - f i) := by
      calc f' a * ∏ i ∈ S, (1 - f' i) ≤ f' a * ∏ i ∈ S, (1 - f i) :=
            mul_le_mul_of_nonneg_left hle (by linarith)
        _ ≤ v * f a * ∏ i ∈ S, (1 - f i) := mul_le_mul_of_nonneg_right hav hA
    nlinarith

lemma pot_elementWeight_update {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (s : T) (δ : ℝ) (e : E) :
    elementWeight inst (Function.update w s (w s + δ)) e
      = elementWeight inst w e + (if s ∈ inst.elemSets e then δ else 0) := by
  unfold elementWeight
  have : ∀ t, Function.update w s (w s + δ) t = w t + (if t = s then δ else 0) := by
    intro t
    by_cases h : t = s
    · subst h; simp
    · simp [Function.update_of_ne h, h]
  simp only [this, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

lemma pot_fval_update {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (w : T → ℝ) (s : T) (δ : ℝ) (hδ : 0 ≤ δ)
    (e : E) :
    fval inst α w e ≤ fval inst α (Function.update w s (w s + δ)) e ∧
    fval inst α (Function.update w s (w s + δ)) e ≤ Real.exp (α * δ) * fval inst α w e ∧
    (s ∉ inst.elemSets e → fval inst α (Function.update w s (w s + δ)) e = fval inst α w e) ∧
    fval inst α (Function.update w s (w s + δ)) e ≤ 1 ∧ 0 ≤ fval inst α w e := by
  unfold fval
  rw [pot_elementWeight_update]
  have hg : 0 < Real.exp (-α + α * elementWeight inst w e) := Real.exp_pos _
  have hv : 1 ≤ Real.exp (α * δ) := Real.one_le_exp (mul_nonneg hα hδ)
  refine ⟨?_, ?_, ?_, min_le_left _ _, le_min zero_le_one hg.le⟩
  · by_cases hs : s ∈ inst.elemSets e
    · simp only [hs, if_true]
      apply min_le_min le_rfl
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα hδ]
    · simp [hs]
  · by_cases hs : s ∈ inst.elemSets e
    · simp only [hs, if_true]
      have : Real.exp (-α + α * (elementWeight inst w e + δ))
          = Real.exp (α * δ) * Real.exp (-α + α * elementWeight inst w e) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      set g := Real.exp (-α + α * elementWeight inst w e)
      set v := Real.exp (α * δ)
      rcases le_total g 1 with h | h
      · rw [min_eq_right h]; exact min_le_right _ _
      · rw [min_eq_left h]
        calc min 1 (v * g) ≤ 1 := min_le_left _ _
          _ ≤ v * 1 := by linarith
    · simp only [hs, if_false, add_zero]
      have : (1:ℝ) ≤ Real.exp (α * δ) := hv
      have h0 : 0 ≤ min 1 (Real.exp (-α + α * elementWeight inst w e)) := le_min zero_le_one hg.le
      nlinarith
  · intro hs
    simp [hs]

lemma pot_potential2_update_not_mem {T : Type*} [Fintype T] [DecidableEq T]
    (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) (hs : s ∉ C) :
    potential2 α OPT (Function.update w s (w s + δ)) (insert s C)
      = 2 * Real.exp (-(α * δ)) * potential2 α OPT w C := by
  unfold potential2
  have key : ∑ t, (Real.log 2 * (if t ∈ insert s C then (1:ℝ) else 0)
        - α * Function.update w s (w s + δ) t) - (OPT : ℝ)
      = (∑ t, (Real.log 2 * (if t ∈ C then (1:ℝ) else 0) - α * w t) - (OPT : ℝ))
        + (Real.log 2 - α * δ) := by
    have : ∀ t, (Real.log 2 * (if t ∈ insert s C then (1:ℝ) else 0)
        - α * Function.update w s (w s + δ) t)
        = (Real.log 2 * (if t ∈ C then (1:ℝ) else 0) - α * w t)
          + (if t = s then Real.log 2 - α * δ else 0) := by
      intro t
      by_cases h : t = s
      · subst h; simp [hs]; ring
      · simp [Function.update_of_ne h, h]
    simp only [this, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
    ring
  have h2 : Real.exp (Real.log 2 - α * δ) = 2 * Real.exp (-(α * δ)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
  rw [key, Real.exp_add _ (Real.log 2 - α * δ), h2]
  ring

lemma pot_potential2_update {T : Type*} [Fintype T] [DecidableEq T]
    (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) :
    potential2 α OPT (Function.update w s (w s + δ)) C
      = Real.exp (-(α * δ)) * potential2 α OPT w C := by
  unfold potential2
  have key : ∑ t, (Real.log 2 * (if t ∈ C then (1:ℝ) else 0)
        - α * Function.update w s (w s + δ) t) - (OPT : ℝ)
      = (∑ t, (Real.log 2 * (if t ∈ C then (1:ℝ) else 0) - α * w t) - (OPT : ℝ))
        + (-(α * δ)) := by
    have : ∀ t, (Real.log 2 * (if t ∈ C then (1:ℝ) else 0)
        - α * Function.update w s (w s + δ) t)
        = (Real.log 2 * (if t ∈ C then (1:ℝ) else 0) - α * w t)
          + (if t = s then -(α * δ) else 0) := by
      intro t
      by_cases h : t = s
      · subst h; simp; ring
      · simp [Function.update_of_ne h, h]
    simp only [this, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
    ring
  rw [key, Real.exp_add]
  ring


open Classical in
lemma pot_p1_split {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (C : Finset T) (s : T) :
    potential1 inst α w C
      = 1 - (∏ e ∈ (Finset.univ.filter (fun e => ¬ coveredBy inst C e)).filter
              (fun e => s ∉ inst.elemSets e), (1 - fval inst α w e))
          * ∏ e ∈ (Finset.univ.filter (fun e => ¬ coveredBy inst C e)).filter
              (fun e => s ∈ inst.elemSets e), (1 - fval inst α w e) := by
  unfold potential1
  rw [← Finset.prod_filter_not_mul_prod_filter (s := Finset.univ.filter (fun e => ¬ coveredBy inst C e))
    (p := fun e => s ∈ inst.elemSets e)]

open Classical in
lemma pot_p1_insert {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (C : Finset T) (s : T) :
    potential1 inst α w (insert s C)
      = 1 - ∏ e ∈ (Finset.univ.filter (fun e => ¬ coveredBy inst C e)).filter
              (fun e => s ∉ inst.elemSets e), (1 - fval inst α w e) := by
  unfold potential1
  have hset : Finset.univ.filter (fun e => ¬ coveredBy inst (insert s C) e)
      = (Finset.univ.filter (fun e => ¬ coveredBy inst C e)).filter
              (fun e => s ∉ inst.elemSets e) := by
    ext e
    have key : coveredBy inst (insert s C) e ↔ coveredBy inst C e ∨ s ∈ inst.elemSets e := by
      constructor
      · rintro ⟨t, ht, htC⟩
        rcases Finset.mem_insert.mp htC with rfl | htC
        · exact Or.inr ht
        · exact Or.inl ⟨t, ht, htC⟩
      · rintro (⟨t, ht, htC⟩ | h)
        · exact ⟨t, ht, Finset.mem_insert_of_mem htC⟩
        · exact ⟨s, h, Finset.mem_insert_self _ _⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, key]
    tauto
  rw [hset]

lemma pot_pos {T : Type*} [Fintype T] [DecidableEq T] (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) :
    0 < potential2 α OPT w C := Real.exp_pos _

open Classical in
lemma pot_core_ii {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (OPT : ℕ)
    (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) (hδ : 0 ≤ δ) :
    potential inst α OPT (Function.update w s (w s + δ)) (insert s C) ≤ potential inst α OPT w C ∨
    potential inst α OPT (Function.update w s (w s + δ)) C ≤ potential inst α OPT w C := by
  set w' := Function.update w s (w s + δ) with hw'
  set S₀ := Finset.univ.filter (fun e => ¬ coveredBy inst C e) with hS₀
  set Bs := S₀.filter (fun e => s ∉ inst.elemSets e) with hBs
  set As := S₀.filter (fun e => s ∈ inst.elemSets e) with hAs
  have hf := fun e => pot_fval_update inst α hα w s δ hδ e
  have hX := pot_pos α OPT w C
  have hu0 : 0 < Real.exp (-(α * δ)) := Real.exp_pos _
  have hu1 : Real.exp (-(α * δ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hα hδ])
  have hBeq : ∏ e ∈ Bs, (1 - fval inst α w' e) = ∏ e ∈ Bs, (1 - fval inst α w e) := by
    apply Finset.prod_congr rfl
    intro e he
    rw [(hf e).2.2.1 (Finset.mem_filter.mp he).2]
  have hsplit := pot_p1_split inst α w C s
  have hsplit' := pot_p1_split inst α w' C s
  rw [← hS₀, ← hBs, ← hAs] at hsplit hsplit'
  rw [hBeq] at hsplit'
  set P := ∏ e ∈ Bs, (1 - fval inst α w e) with hP
  have hf1 : ∀ e, fval inst α w e ≤ 1 := fun e => min_le_left _ _
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun e he => by
    have := hf1 e; linarith)
  have hv1 : 1 ≤ Real.exp (α * δ) := Real.one_le_exp (mul_nonneg hα hδ)
  have huv : Real.exp (-(α * δ)) * Real.exp (α * δ) = 1 := by
    rw [← Real.exp_add]; simp
  set u := Real.exp (-(α * δ)) with hu
  set v := Real.exp (α * δ) with hv
  set X := potential2 α OPT w C with hXdef
  have hp2 : potential2 α OPT w' C = u * X := pot_potential2_update α OPT w C s δ
  by_cases hsC : s ∈ C
  · right
    have hAs_empty : As = ∅ := by
      rw [hAs, Finset.filter_eq_empty_iff]
      intro e he hse
      have := (Finset.mem_filter.mp he).2
      exact this ⟨s, hse, hsC⟩
    rw [hAs_empty, Finset.prod_empty, mul_one] at hsplit hsplit'
    unfold potential
    rw [hsplit, hsplit', hp2]
    nlinarith [mul_le_mul_of_nonneg_right hu1 hX.le]
  · have hp2' : potential2 α OPT w' (insert s C) = 2 * u * X :=
      pot_potential2_update_not_mem α OPT w C s δ hsC
    have hins := pot_p1_insert inst α w' C s
    rw [← hS₀, ← hBs, hBeq] at hins
    set Q := ∏ e ∈ As, (1 - fval inst α w e) with hQ
    set Q' := ∏ e ∈ As, (1 - fval inst α w' e) with hQ'
    have hclamp : 1 - Q' ≤ v * (1 - Q) := by
      apply pot_prod_clamp As (fun e => fval inst α w e) (fun e => fval inst α w' e) v
      · intro e _; exact (hf e).2.2.2.2
      · intro e _; exact (hf e).1
      · intro e _; exact (hf e).2.2.2.1
      · intro e _; exact (hf e).2.1
    have hclamp2 : u - u * Q' ≤ 1 - Q := by
      have h1 := mul_le_mul_of_nonneg_left hclamp hu0.le
      have h2 : u * (v * (1 - Q)) = 1 - Q := by rw [← mul_assoc, huv, one_mul]
      nlinarith
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    unfold potential at h1 h2
    rw [hins, hp2'] at h1
    rw [hsplit', hp2] at h2
    rw [hsplit] at h1 h2
    have e1 : 0 ≤ P * (1 - u + u * Q' - Q) := mul_nonneg hP0 (by linarith)
    have e2 : 0 ≤ X * (1 - u) ^ 2 := mul_nonneg hX.le (sq_nonneg _)
    nlinarith [mul_pos hu0 hu0, mul_nonneg hu0.le (sub_nonneg.mpr hu1)]

end BNCovPack.SetCover

open BNCovPack.SetCover
open OnlinePrimalDual.OnlineSetCover

theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (OPT : ℕ)
    (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) (hδ : 0 ≤ δ) :
    potential inst α OPT (Function.update w s (w s + δ)) (insert s C) ≤ potential inst α OPT w C ∨
    potential inst α OPT (Function.update w s (w s + δ)) C ≤ potential inst α OPT w C := by
  exact pot_core_ii inst α hα OPT w C s δ hδ
