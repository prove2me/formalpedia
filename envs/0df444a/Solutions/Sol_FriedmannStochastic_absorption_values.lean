-- Prove2me | solution 1 for FriedmannStochastic.absorption_values
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T01:39:51.822817+00:00
-- url     : https://prove2.me/submissions/8752534c-9ae5-46e9-a463-b202ea989319

import Definitions.Def_friedmann_payoff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

section Mod_stochastic_semantics
set_option autoImplicit false

namespace FriedmannStochastic

open scoped BigOperators
open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

lemma fin3_eq_two {r : Fin 3} (h0 : r ≠ 0) (h1 : r ≠ 1) : r = 2 := by
  ext
  have hlt := r.isLt
  have h0' : r.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h1' : r.val ≠ 1 := fun h => h1 (Fin.ext h)
  omega

omit [Fintype V] in
lemma transition_win (G : Game V) (σ τ : V → V) (w : V) :
    transition G σ τ G.win w = 0 := by
  unfold transition
  simp

omit [Fintype V] in
lemma transition_lose (G : Game V) (σ τ : V → V) (w : V) :
    transition G σ τ G.lose w = 0 := by
  unfold transition
  simp

lemma transition_nonneg (G : Game V) (hG : WellFormed G) (σ τ : V → V) (v w : V) :
    0 ≤ transition G σ τ v w := by
  unfold transition
  by_cases hterm : v = G.win ∨ v = G.lose
  · simp [hterm]
  · rw [if_neg hterm]
    by_cases h0 : G.role v = 0
    · rw [if_pos h0]
      split_ifs <;> norm_num
    · rw [if_neg h0]
      by_cases h1 : G.role v = 1
      · rw [if_pos h1]
        split_ifs <;> norm_num
      · rw [if_neg h1]
        have hdec : Decision G 2 v :=
          ⟨fun h => hterm (Or.inl h), fun h => hterm (Or.inr h), fin3_eq_two h0 h1⟩
        exact (hG.2.2.2.1 v w hdec).1

lemma transition_row_sum (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    {v : V} (hwin : v ≠ G.win) (hlose : v ≠ G.lose) :
    ∑ w, transition G σ τ v w = 1 := by
  have hterm : ¬ (v = G.win ∨ v = G.lose) := by
    rintro (rfl | rfl)
    · exact hwin rfl
    · exact hlose rfl
  by_cases h0 : G.role v = 0
  · have hcongr : ∀ w, transition G σ τ v w = if σ v = w then 1 else 0 := by
      intro w
      unfold transition
      simp [hterm, h0]
    simp [hcongr]
  · by_cases h1 : G.role v = 1
    · have hcongr : ∀ w, transition G σ τ v w = if τ v = w then 1 else 0 := by
        intro w
        unfold transition
        simp [hterm, h1]
      simp [hcongr]
    · have hcongr : ∀ w, transition G σ τ v w = G.probability v w := by
        intro w
        unfold transition
        simp [hterm, h0, h1]
      simp only [hcongr]
      exact hG.2.2.2.2.1 v ⟨hwin, hlose, fin3_eq_two h0 h1⟩

lemma eq_max_of_step (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (f : V → ℚ) (M : ℚ)
    (hbound : ∀ z, f z ≤ M)
    (hsub : ∀ u, u ≠ G.win → u ≠ G.lose → f u ≤ ∑ z, transition G σ τ u z * f z)
    {u w : V} (hu : f u = M) (hstep : 0 < transition G σ τ u w) :
    f w = M := by
  have hwin : u ≠ G.win := by
    rintro rfl
    rw [transition_win] at hstep
    exact lt_irrefl 0 hstep
  have hlose : u ≠ G.lose := by
    rintro rfl
    rw [transition_lose] at hstep
    exact lt_irrefl 0 hstep
  by_contra hne
  have hlt : f w < M := lt_of_le_of_ne (hbound w) hne
  have hsum_lt : ∑ z, transition G σ τ u z * f z < ∑ z, transition G σ τ u z * M := by
    apply Finset.sum_lt_sum
    · intro z _
      exact mul_le_mul_of_nonneg_left (hbound z) (transition_nonneg G hG σ τ u z)
    · exact ⟨w, Finset.mem_univ w, mul_lt_mul_of_pos_left hlt hstep⟩
  rw [← Finset.sum_mul, transition_row_sum G hG σ τ hwin hlose, one_mul] at hsum_lt
  have hle := hsub u hwin hlose
  linarith

lemma eq_max_of_reflTransGen (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (f : V → ℚ) (M : ℚ)
    (hbound : ∀ z, f z ≤ M)
    (hsub : ∀ u, u ≠ G.win → u ≠ G.lose → f u ≤ ∑ z, transition G σ τ u z * f z)
    {u v : V} (hu : f u = M)
    (hreach : Relation.ReflTransGen (fun a b => 0 < transition G σ τ a b) u v) :
    f v = M := by
  induction hreach with
  | refl => exact hu
  | tail _ hstep ih => exact eq_max_of_step G hG σ τ f M hbound hsub ih hstep

lemma le_max_terminals (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (hσ : Legal G 0 σ) (hτ : Legal G 1 τ)
    (f : V → ℚ)
    (hsub : ∀ u, u ≠ G.win → u ≠ G.lose → f u ≤ ∑ z, transition G σ τ u z * f z)
    (v : V) :
    f v ≤ max (f G.win) (f G.lose) := by
  have hne : (Finset.univ : Finset V).Nonempty := ⟨v, Finset.mem_univ v⟩
  set M := Finset.univ.sup' hne f
  have hbound : ∀ z, f z ≤ M := fun z => Finset.le_sup' f (Finset.mem_univ z)
  obtain ⟨u₀, _, hu₀⟩ := Finset.exists_mem_eq_sup' hne f
  rcases hG.2.2.2.2.2 σ τ hσ hτ u₀ with hwin | hlose
  · have hM := eq_max_of_reflTransGen G hG σ τ f M hbound hsub hu₀.symm hwin
    exact le_trans (hbound v) (by rw [← hM]; exact le_max_left _ _)
  · have hM := eq_max_of_reflTransGen G hG σ τ f M hbound hsub hu₀.symm hlose
    exact le_trans (hbound v) (by rw [← hM]; exact le_max_right _ _)

lemma sub_transition_mulVec_apply (G : Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    ((1 - transition G σ τ) *ᵥ x) v = x v - ∑ w, transition G σ τ v w * x w := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
  rfl

lemma one_sub_transition_det_ne_zero (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (hσ : Legal G 0 σ) (hτ : Legal G 1 τ) :
    (1 - transition G σ τ).det ≠ 0 := by
  intro hdet
  rcases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with ⟨x, hxne, hx⟩
  have hfp : ∀ v, x v = ∑ w, transition G σ τ v w * x w := by
    intro v
    have hv : ((1 - transition G σ τ) *ᵥ x) v = 0 := congrFun hx v
    rw [sub_transition_mulVec_apply] at hv
    linarith
  have hx_win : x G.win = 0 := by
    rw [hfp G.win]
    simp [transition_win]
  have hx_lose : x G.lose = 0 := by
    rw [hfp G.lose]
    simp [transition_lose]
  have hle : ∀ v, x v ≤ 0 := by
    intro v
    have h := le_max_terminals G hG σ τ hσ hτ x (fun u _ _ => le_of_eq (hfp u)) v
    rw [hx_win, hx_lose, max_self] at h
    exact h
  have hge : ∀ v, 0 ≤ x v := by
    intro v
    have hsub_neg : ∀ u, u ≠ G.win → u ≠ G.lose →
        (-x) u ≤ ∑ z, transition G σ τ u z * (-x) z := by
      intro u _ _
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, ← hfp u, le_rfl]
    have h := le_max_terminals G hG σ τ hσ hτ (-x) hsub_neg v
    simp only [Pi.neg_apply, hx_win, hx_lose, neg_zero, max_self] at h
    linarith
  apply hxne
  ext v
  exact le_antisymm (hle v) (hge v)

theorem absorption_values (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (hσ : Legal G 0 σ) (hτ : Legal G 1 τ) :
    (1 - transition G σ τ).det ≠ 0 ∧
    playValue G σ τ G.win = 1 ∧ playValue G σ τ G.lose = 0 ∧
    (∀ v, 0 ≤ playValue G σ τ v ∧ playValue G σ τ v ≤ 1) ∧
    (∀ v, v ≠ G.win → v ≠ G.lose →
      playValue G σ τ v = ∑ w, transition G σ τ v w * playValue G σ τ w) := by
  have hdet : (1 - transition G σ τ).det ≠ 0 :=
    one_sub_transition_det_ne_zero G hG σ τ hσ hτ
  have hunit : IsUnit (1 - transition G σ τ).det := isUnit_iff_ne_zero.mpr hdet
  have hmul : (1 - transition G σ τ) *ᵥ playValue G σ τ =
      fun v => if v = G.win then 1 else 0 := by
    unfold playValue
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have heq : ∀ v, playValue G σ τ v - ∑ w, transition G σ τ v w * playValue G σ τ w =
      if v = G.win then 1 else 0 := by
    intro v
    rw [← sub_transition_mulVec_apply, hmul]
  have hwin : playValue G σ τ G.win = 1 := by
    have h := heq G.win
    simp only [transition_win, zero_mul, Finset.sum_const_zero, sub_zero, ↓reduceIte] at h
    exact h
  have hlose : playValue G σ τ G.lose = 0 := by
    have h := heq G.lose
    have hne : G.lose ≠ G.win := hG.1.symm
    simp only [transition_lose, zero_mul, Finset.sum_const_zero, sub_zero, hne, ↓reduceIte] at h
    exact h
  have hharm : ∀ v, v ≠ G.win → v ≠ G.lose →
      playValue G σ τ v = ∑ w, transition G σ τ v w * playValue G σ τ w := by
    intro v hvw _
    have h := heq v
    rw [if_neg hvw] at h
    linarith
  have hbounds : ∀ v, 0 ≤ playValue G σ τ v ∧ playValue G σ τ v ≤ 1 := by
    intro v
    constructor
    · have hsub_neg : ∀ u, u ≠ G.win → u ≠ G.lose →
          (-playValue G σ τ) u ≤ ∑ z, transition G σ τ u z * (-playValue G σ τ) z := by
        intro u huw hul
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, ← hharm u huw hul, le_rfl]
      have h := le_max_terminals G hG σ τ hσ hτ (-playValue G σ τ) hsub_neg v
      simp only [Pi.neg_apply, hwin, hlose, neg_zero] at h
      have hmax : max (-1 : ℚ) 0 = 0 := by norm_num
      linarith
    · have h := le_max_terminals G hG σ τ hσ hτ (playValue G σ τ)
        (fun u huw hul => le_of_eq (hharm u huw hul)) v
      rw [hwin, hlose] at h
      have hmax : max (1 : ℚ) 0 = 1 := by norm_num
      linarith
  exact ⟨hdet, hwin, hlose, hbounds, hharm⟩

theorem solution_stochastic_semantics {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (hσ : Legal G 0 σ) (hτ : Legal G 1 τ) :
    (1 - transition G σ τ).det ≠ 0 ∧
    playValue G σ τ G.win = 1 ∧ playValue G σ τ G.lose = 0 ∧
    (∀ v, 0 ≤ playValue G σ τ v ∧ playValue G σ τ v ≤ 1) ∧
    (∀ v, v ≠ G.win → v ≠ G.lose →
      playValue G σ τ v = ∑ w, transition G σ τ v w * playValue G σ τ w) :=
  absorption_values G hG σ τ hσ hτ

end FriedmannStochastic

end Mod_stochastic_semantics

open FriedmannStochastic in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (hσ : Legal G 0 σ) (hτ : Legal G 1 τ) :
    (1 - transition G σ τ).det ≠ 0 ∧
    playValue G σ τ G.win = 1 ∧ playValue G σ τ G.lose = 0 ∧
    (∀ v, 0 ≤ playValue G σ τ v ∧ playValue G σ τ v ≤ 1) ∧
    (∀ v, v ≠ G.win → v ≠ G.lose →
      playValue G σ τ v = ∑ w, transition G σ τ v w * playValue G σ τ w) := by
  first
    | exact FriedmannStochastic.absorption_values
    | (apply FriedmannStochastic.absorption_values <;> assumption)
