-- Prove2me | solution 1 for DistancePreserver934.Exact.equation_26
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:13:06.949577+00:00
-- url     : https://prove2.me/submissions/3ac938b8-52c6-4b62-a0cc-dcafc0129443

import Theorems.Thm_DistancePreserver934_Exact_equation_26_reachable
import Theorems.Thm_DistancePreserver934_Exact_lemma_2

set_option autoImplicit false
open Classical DistancePreserver934.Exact

private lemma normalize_demands {V : Type} [Fintype V] (G : SimpleGraph V) (P : Finset (Sym2 V)) :
    ∃ R ⊆ P, IsDemandSet G R ∧
      ∀ H : SimpleGraph V, IsPreserver G H R ↔ IsPreserver G H P := by
  classical
  let R := P.filter (fun q => ∀ s t : V, s(s,t) = q → s ≠ t ∧ G.Reachable s t)
  refine ⟨R, Finset.filter_subset _ _, ?_, ?_⟩
  · intro s t hst
    exact (Finset.mem_filter.mp hst).2 s t rfl
  · intro H
    constructor
    · rintro ⟨hHG,hpres⟩
      refine ⟨hHG, ?_⟩
      intro s t hst
      by_cases heq : s = t
      · subst t; simp
      by_cases hr : G.Reachable s t
      · apply hpres s t
        refine Finset.mem_filter.mpr ⟨hst, ?_⟩
        intro a b hab
        rcases Sym2.eq_iff.mp hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨heq,hr⟩
        · exact ⟨Ne.symm heq,hr.symm⟩
      · have htop : G.edist s t = ⊤ := SimpleGraph.edist_eq_top_of_not_reachable hr
        apply le_antisymm
        · rw [htop]; exact le_top
        · exact SimpleGraph.edist_anti hHG
    · rintro ⟨hHG,hpres⟩
      exact ⟨hHG,fun s t hst => hpres s t (Finset.mem_filter.mp hst).1⟩

private lemma minimal_normalize {V : Type} [Fintype V] (G H : SimpleGraph V)
    (P R : Finset (Sym2 V)) (heq : ∀ H, IsPreserver G H R ↔ IsPreserver G H P)
    (hH : IsMinimalPreserver G H P) : IsMinimalPreserver G H R := by
  exact ⟨(heq H).mpr hH.1,fun e he hdel => hH.2 e he ((heq _).mp hdel)⟩

theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ (P.card : ℝ) → (P.card : ℝ) ≤ (Fintype.card V : ℝ) →
      IsMinimalPreserver G H P →
      (numEdges H : ℝ) ≤
        C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * (P.card : ℝ) ^ ((4 : ℝ) / 9) := by
  obtain ⟨C₁,hC₁,hbound⟩ := DistancePreserver934.Exact.equation_26_reachable
  obtain ⟨C₂,hC₂,hclassical⟩ := DistancePreserver934.Exact.lemma_2
  refine ⟨C₁+2*C₂,by positivity,?_⟩
  intro V inst G H P hlo hhi hH
  classical
  by_cases hz : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
    have hE : numEdges H = 0 := by
      unfold numEdges
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      induction e using Sym2.ind with
      | _ a b => exact isEmptyElim a
    simp [hE, hz, Real.zero_rpow]
  let n : ℝ := Fintype.card V
  have hn1 : 1 ≤ n := by
    change 1 ≤ (Fintype.card V : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hn : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  obtain ⟨R,hRP,hR,heq⟩ := normalize_demands G P
  have hHR := minimal_normalize G H P R heq hH
  have hcard : (R.card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card hRP
  by_cases hlarge : n^((1:ℝ)/4) ≤ (R.card : ℝ)
  · have h := hbound V G H R hR hlarge (hcard.trans hhi) hHR
    calc
      _ ≤ C₁*n^((8:ℝ)/9)*(R.card : ℝ)^((4:ℝ)/9) := h
      _ ≤ C₁*n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by
        gcongr
      _ ≤ (C₁+2*C₂)*n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by
        gcongr; linarith
  have hsmall := (lt_of_not_ge hlarge).le
  have hCE : (numEdges H : ℝ) ≤ 2*C₂*n := by
    have hb := hclassical V G H R hR hHR
    have hmul : (R.card : ℝ)*Real.sqrt n ≤ n := by
      calc
        _ ≤ n^((1:ℝ)/4)*n^((1:ℝ)/2) := by
          rw [Real.sqrt_eq_rpow]
          exact mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hn.le _)
        _ = n^((3:ℝ)/4) := by rw [← Real.rpow_add hn]; norm_num
        _ ≤ n^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        _ = n := Real.rpow_one _
    change (numEdges H : ℝ) ≤ C₂*(n+(R.card : ℝ)*Real.sqrt n) at hb
    nlinarith
  have hnmain : n ≤ n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by
    calc
      n = n^((8:ℝ)/9)*(n^((1:ℝ)/4))^((4:ℝ)/9) := by
        rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]; norm_num
      _ ≤ n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn.le _)
        exact Real.rpow_le_rpow (Real.rpow_nonneg hn.le _) hlo (by norm_num)
  calc
    _ ≤ 2*C₂*n := hCE
    _ ≤ 2*C₂*(n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9)) :=
      mul_le_mul_of_nonneg_left hnmain (by positivity)
    _ ≤ (C₁+2*C₂)*n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by
      have hprod : 0 ≤ n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by positivity
      nlinarith
