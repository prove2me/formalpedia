-- Prove2me | solution 1 for FriedmannParity.exponential_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T04:01:48.019318+00:00
-- url     : https://prove2.me/submissions/26eb7c60-fde7-4d89-a48c-a9b447b9dad4

import Theorems.Thm_FriedmannParity_exponential_payoff
import Definitions.Def_friedmann_payoff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false

section Mod_discounted_bellman
set_option autoImplicit false

namespace FriedmannDiscounted

open scoped BigOperators
open Matrix

lemma transition_mulVec {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    (transition G σ τ *ᵥ x) v = x (if G.arena.owner v = false then σ v else τ v) := by
  classical
  dsimp [transition, mulVec, dotProduct]
  simp

lemma one_sub_discount_transition_mulVec {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    ((1 - G.discount • transition G σ τ) *ᵥ x) v =
      x v - G.discount * x (if G.arena.owner v = false then σ v else τ v) := by
  rw [sub_mulVec, one_mulVec, Pi.sub_apply, ← transition_mulVec G σ τ x v]
  congr 1
  dsimp [mulVec, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma isUnit_det_one_sub_discount_transition {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V) :
    IsUnit (1 - G.discount • transition G σ τ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  rcases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with ⟨x, hxne, hx⟩
  have hfp : ∀ v, x v = G.discount * x (if G.arena.owner v = false then σ v else τ v) := by
    intro v
    have hv := congrFun hx v
    rw [Pi.zero_apply, one_sub_discount_transition_mulVec] at hv
    linarith
  have hne : (Finset.univ : Finset V).Nonempty := by
    by_contra hempty
    apply hxne
    ext v
    exact False.elim (hempty ⟨v, Finset.mem_univ v⟩)
  set M := Finset.univ.sup' hne (fun v => |x v|)
  have hM : ∀ v, |x v| ≤ M := fun v => Finset.le_sup' (fun u => |x u|) (Finset.mem_univ v)
  obtain ⟨v₀, _, hv₀⟩ := Finset.exists_mem_eq_sup' hne (fun v => |x v|)
  have hβ0 : 0 < G.discount := hG.2.1
  have hβ1 : G.discount < 1 := hG.2.2
  by_cases hMpos : 0 < M
  · have hstep : |x v₀| = G.discount * |x (if G.arena.owner v₀ = false then σ v₀ else τ v₀)| := by
      rw [hfp v₀, abs_mul, abs_of_pos hβ0]
    have hle : G.discount * |x (if G.arena.owner v₀ = false then σ v₀ else τ v₀)| ≤ G.discount * M :=
      mul_le_mul_of_nonneg_left (hM _) (le_of_lt hβ0)
    have hlt : G.discount * M < 1 * M :=
      mul_lt_mul_of_pos_right hβ1 hMpos
    linarith
  · apply hxne
    ext v
    have h1 : |x v| ≤ 0 := le_trans (hM v) (not_lt.mp hMpos)
    exact abs_nonpos_iff.mp h1

theorem discounted_bellman {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V) :
    (∀ v, playValue G σ τ v = G.reward v + G.discount *
      playValue G σ τ (if G.arena.owner v = false then σ v else τ v)) ∧
    ∀ x : V → ℚ,
      (∀ v, x v = G.reward v + G.discount *
        x (if G.arena.owner v = false then σ v else τ v)) → x = playValue G σ τ := by
  have hunit := isUnit_det_one_sub_discount_transition G hG σ τ
  set A := 1 - G.discount • transition G σ τ
  constructor
  · intro v
    have hmul : A *ᵥ playValue G σ τ = G.reward := by
      unfold playValue
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, one_mulVec]
    have hv := congrFun hmul v
    rw [one_sub_discount_transition_mulVec] at hv
    linarith
  · intro x hx
    have hmul : A *ᵥ x = G.reward := by
      ext v
      rw [one_sub_discount_transition_mulVec]
      linarith [hx v]
    unfold playValue
    rw [← hmul, mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, one_mulVec]

end FriedmannDiscounted

end Mod_discounted_bellman

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

section Mod_stochastic
set_option autoImplicit false

namespace FriedmannParity

open scoped BigOperators

/-! ### Part 1: General Characterization of `FriedmannScalar.value` -/

lemma scalar_value_eq_of_isMin {V : Type} [Fintype V] [DecidableEq V]
    (M : FriedmannScalar.Model V) (σ : V → V) (v : V) (a : ℚ)
    (hex : ∃ τ, M.minLegal τ ∧ M.payoff σ τ v = a)
    (hle : ∀ τ, M.minLegal τ → a ≤ M.payoff σ τ v) :
    FriedmannScalar.value M σ v = a := by
  have h : ∃ a' : ℚ,
      (∃ τ, M.minLegal τ ∧ M.payoff σ τ v = a') ∧
        ∀ τ, M.minLegal τ → a' ≤ M.payoff σ τ v := ⟨a, hex, hle⟩
  unfold FriedmannScalar.value
  rw [dif_pos h]
  rcases Classical.choose_spec h with ⟨⟨τ₁, hτ₁, heq₁⟩, hle₁⟩
  rcases hex with ⟨τ₂, hτ₂, heq₂⟩
  have h1 : Classical.choose h ≤ a := by
    rw [← heq₂]
    exact hle₁ τ₂ hτ₂
  have h2 : a ≤ Classical.choose h := by
    rw [← heq₁]
    exact hle τ₁ hτ₁
  exact le_antisymm h1 h2

lemma exists_legal_true {N : ℕ} (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) :
    ∃ τ : Fin N → Fin N, Legal G.arena true τ := by
  refine ⟨fun v => Classical.choose (hG.1 v), ?_⟩
  intro v _
  exact Classical.choose_spec (hG.1 v)

lemma discounted_value_spec {N : ℕ} (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) (σ : Fin N → Fin N) (v : Fin N) :
    (∃ τ, Legal G.arena true τ ∧
      FriedmannDiscounted.playValue G σ τ v =
        FriedmannScalar.value (FriedmannDiscounted.model G) σ v) ∧
    (∀ τ, Legal G.arena true τ →
      FriedmannScalar.value (FriedmannDiscounted.model G) σ v ≤
        FriedmannDiscounted.playValue G σ τ v) := by
  classical
  rcases exists_legal_true G hG with ⟨τ₀, hτ₀⟩
  let S : Finset (Fin N → Fin N) := Finset.univ.filter (fun τ => Legal G.arena true τ)
  have hS : S.Nonempty := ⟨τ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ τ₀, hτ₀⟩⟩
  set a := S.inf' hS (fun τ => FriedmannDiscounted.playValue G σ τ v)
  obtain ⟨τ_min, hτ_min_mem, hτ_min_eq⟩ :=
    Finset.exists_mem_eq_inf' hS (fun τ => FriedmannDiscounted.playValue G σ τ v)
  have hτ_min : Legal G.arena true τ_min := (Finset.mem_filter.mp hτ_min_mem).2
  have hle : ∀ τ, Legal G.arena true τ → a ≤ FriedmannDiscounted.playValue G σ τ v := by
    intro τ hτ
    exact Finset.inf'_le (fun τ' => FriedmannDiscounted.playValue G σ τ' v)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ τ, hτ⟩)
  have hval : FriedmannScalar.value (FriedmannDiscounted.model G) σ v = a :=
    scalar_value_eq_of_isMin (FriedmannDiscounted.model G) σ v a
      ⟨τ_min, hτ_min, hτ_min_eq.symm⟩ hle
  rw [hval]
  exact ⟨⟨τ_min, hτ_min, hτ_min_eq.symm⟩, hle⟩

/-! ### Part 2: Positivity of `N` and Reward Scaling -/

lemma pos_of_hardInstance {N : ℕ} {G : FriedmannDiscounted.Game (Fin N)}
    {ι : Fin N → Fin N} {step : (Fin N → Fin N) → (Fin N → Fin N) → Prop}
    {k : ℕ} (hk : 0 < k)
    (hHard : FriedmannScalar.HardInstance (FriedmannDiscounted.model G) ι step k) :
    0 < N := by
  rcases hHard.2.1 with ⟨T, run, hrun⟩
  have hTk : k ≤ T := hHard.2.2 T run hrun
  have hT0 : 0 < T := lt_of_lt_of_le hk hTk
  rcases (hrun.2.2.1 0 hT0).1 with ⟨v, _, _⟩
  exact lt_of_le_of_lt (Nat.zero_le v.val) v.isLt

theorem finUnivNonempty {N : ℕ} (hN : 0 < N) : (Finset.univ : Finset (Fin N)).Nonempty :=
  ⟨⟨0, hN⟩, Finset.mem_univ _⟩

noncomputable def lowerBound {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) : ℚ :=
  Finset.univ.inf' (finUnivNonempty hN) G.reward - 1

noncomputable def upperBound {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) : ℚ :=
  Finset.univ.sup' (finUnivNonempty hN) G.reward + 1

noncomputable def span {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) : ℚ :=
  upperBound hN G - lowerBound hN G

noncomputable def alpha {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) (v : Fin N) : ℚ :=
  (G.reward v - lowerBound hN G) / span hN G

lemma lowerBound_lt_reward {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) (v : Fin N) :
    lowerBound hN G < G.reward v := by
  have h := Finset.inf'_le G.reward (Finset.mem_univ v)
  unfold lowerBound
  linarith

lemma reward_lt_upperBound {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) (v : Fin N) :
    G.reward v < upperBound hN G := by
  have h := Finset.le_sup' G.reward (Finset.mem_univ v)
  unfold upperBound
  linarith

lemma span_pos {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) :
    0 < span hN G := by
  have h1 := lowerBound_lt_reward hN G ⟨0, hN⟩
  have h2 := reward_lt_upperBound hN G ⟨0, hN⟩
  unfold span
  linarith

lemma alpha_pos {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) (v : Fin N) :
    0 < alpha hN G v :=
  div_pos (sub_pos.mpr (lowerBound_lt_reward hN G v)) (span_pos hN G)

lemma alpha_lt_one {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) (v : Fin N) :
    alpha hN G v < 1 := by
  unfold alpha
  rw [div_lt_one (span_pos hN G)]
  unfold span
  linarith [reward_lt_upperBound hN G v]

lemma one_sub_alpha_pos {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) (v : Fin N) :
    0 < 1 - alpha hN G v :=
  sub_pos.mpr (alpha_lt_one hN G v)

lemma alpha_mul_span {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) (v : Fin N) :
    alpha hN G v * span hN G = G.reward v - lowerBound hN G := by
  unfold alpha
  exact div_mul_cancel₀ _ (ne_of_gt (span_pos hN G))

/-! ### Part 3: Vertex Encoding on `Fin (2 * N + 2)` -/

def decNode (N : ℕ) (v : Fin N) : Fin (2 * N + 2) := ⟨v.val, by omega⟩
def randNode (N : ℕ) (v : Fin N) : Fin (2 * N + 2) := ⟨N + v.val, by omega⟩
def winNode (N : ℕ) : Fin (2 * N + 2) := ⟨2 * N, by omega⟩
def loseNode (N : ℕ) : Fin (2 * N + 2) := ⟨2 * N + 1, by omega⟩

def unrand {N : ℕ} (hN : 0 < N) (x : Fin (2 * N + 2)) : Fin N :=
  if h : N ≤ x.val ∧ x.val < 2 * N then ⟨x.val - N, by omega⟩ else ⟨0, hN⟩

@[simp]
lemma decNode_inj {N : ℕ} {u v : Fin N} : decNode N u = decNode N v ↔ u = v := by
  simp [decNode, Fin.ext_iff]

@[simp]
lemma randNode_inj {N : ℕ} {u v : Fin N} : randNode N u = randNode N v ↔ u = v := by
  simp [randNode, Fin.ext_iff]

@[simp]
lemma unrand_randNode {N : ℕ} (hN : 0 < N) (v : Fin N) :
    unrand hN (randNode N v) = v := by
  unfold unrand randNode
  rw [dif_pos (by dsimp; omega)]
  ext
  dsimp
  omega

lemma decNode_ne_randNode {N : ℕ} (u v : Fin N) : decNode N u ≠ randNode N v := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [decNode, randNode] at hval
  omega

lemma decNode_ne_winNode {N : ℕ} (v : Fin N) : decNode N v ≠ winNode N := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [decNode, winNode] at hval
  omega

lemma decNode_ne_loseNode {N : ℕ} (v : Fin N) : decNode N v ≠ loseNode N := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [decNode, loseNode] at hval
  omega

lemma randNode_ne_winNode {N : ℕ} (v : Fin N) : randNode N v ≠ winNode N := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [randNode, winNode] at hval
  omega

lemma randNode_ne_loseNode {N : ℕ} (v : Fin N) : randNode N v ≠ loseNode N := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [randNode, loseNode] at hval
  omega

lemma winNode_ne_loseNode (N : ℕ) : winNode N ≠ loseNode N := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [winNode, loseNode] at hval
  omega

lemma vertex_cases {N : ℕ} (x : Fin (2 * N + 2)) :
    (∃ v : Fin N, x = decNode N v) ∨
    (∃ v : Fin N, x = randNode N v) ∨
    x = winNode N ∨ x = loseNode N := by
  by_cases h1 : x.val < N
  · exact Or.inl ⟨⟨x.val, h1⟩, by ext; rfl⟩
  · by_cases h2 : x.val < 2 * N
    · exact Or.inr (Or.inl ⟨⟨x.val - N, by omega⟩, by ext; dsimp [randNode]; omega⟩)
    · by_cases h3 : x.val = 2 * N
      · exact Or.inr (Or.inr (Or.inl (by ext; exact h3)))
      · exact Or.inr (Or.inr (Or.inr (by ext; dsimp [loseNode]; omega)))

/-! ### Part 4: The Stochastic Game Construction -/

noncomputable def stochGame {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) :
    FriedmannStochastic.Game (Fin (2 * N + 2)) where
  role x :=
    if h : x.val < N then (if G.arena.owner ⟨x.val, h⟩ = false then 0 else 1) else 2
  edge x y :=
    if h : x.val < N then ∃ w : Fin N, y = randNode N w ∧ G.arena.edge ⟨x.val, h⟩ w
    else if h2 : x.val < 2 * N then
      y = decNode N ⟨x.val - N, by omega⟩ ∨ y = winNode N ∨ y = loseNode N
    else False
  probability x y :=
    if h : N ≤ x.val ∧ x.val < 2 * N then
      let v : Fin N := ⟨x.val - N, by omega⟩
      (if y = decNode N v then G.discount else 0) +
      (if y = winNode N then (1 - G.discount) * alpha hN G v else 0) +
      (if y = loseNode N then (1 - G.discount) * (1 - alpha hN G v) else 0)
    else 0
  win := winNode N
  lose := loseNode N

@[simp]
lemma stochGame_win {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) :
    (stochGame hN G).win = winNode N := rfl

@[simp]
lemma stochGame_lose {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) :
    (stochGame hN G).lose = loseNode N := rfl

lemma stochGame_role_decNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (v : Fin N) :
    (stochGame hN G).role (decNode N v) = if G.arena.owner v = false then 0 else 1 := by
  unfold stochGame decNode
  dsimp
  rw [dif_pos v.isLt]

lemma stochGame_role_randNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (v : Fin N) :
    (stochGame hN G).role (randNode N v) = 2 := by
  unfold stochGame randNode
  dsimp
  rw [dif_neg (by omega)]

lemma stochGame_edge_decNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (v : Fin N) (y : Fin (2 * N + 2)) :
    (stochGame hN G).edge (decNode N v) y ↔
      ∃ w : Fin N, y = randNode N w ∧ G.arena.edge v w := by
  unfold stochGame decNode
  dsimp
  rw [dif_pos v.isLt]

lemma stochGame_edge_decNode_randNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (v w : Fin N) :
    (stochGame hN G).edge (decNode N v) (randNode N w) ↔ G.arena.edge v w := by
  rw [stochGame_edge_decNode]
  constructor
  · rintro ⟨w', hw', hedge⟩
    rw [randNode_inj.mp hw']
    exact hedge
  · intro hedge
    exact ⟨w, rfl, hedge⟩

lemma stochGame_edge_randNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (v : Fin N) (y : Fin (2 * N + 2)) :
    (stochGame hN G).edge (randNode N v) y ↔
      y = decNode N v ∨ y = winNode N ∨ y = loseNode N := by
  unfold stochGame randNode
  dsimp
  rw [dif_neg (by omega), dif_pos (by omega)]
  have hv : (⟨N + v.val - N, by omega⟩ : Fin N) = v := by ext; dsimp; omega
  rw [hv]

lemma stochGame_edge_winNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (y : Fin (2 * N + 2)) :
    ¬ (stochGame hN G).edge (winNode N) y := by
  unfold stochGame winNode
  dsimp
  rw [dif_neg (by omega), dif_neg (by omega)]
  exact id

lemma stochGame_edge_loseNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (y : Fin (2 * N + 2)) :
    ¬ (stochGame hN G).edge (loseNode N) y := by
  unfold stochGame loseNode
  dsimp
  rw [dif_neg (by omega), dif_neg (by omega)]
  exact id

lemma stochGame_probability_randNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (v : Fin N) (y : Fin (2 * N + 2)) :
    (stochGame hN G).probability (randNode N v) y =
      (if y = decNode N v then G.discount else 0) +
      (if y = winNode N then (1 - G.discount) * alpha hN G v else 0) +
      (if y = loseNode N then (1 - G.discount) * (1 - alpha hN G v) else 0) := by
  unfold stochGame randNode
  dsimp
  rw [dif_pos (by omega)]
  have hv : (⟨N + v.val - N, by omega⟩ : Fin N) = v := by ext; dsimp; omega
  rw [hv]

lemma decision_zero_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (x : Fin (2 * N + 2)) :
    FriedmannStochastic.Decision (stochGame hN G) 0 x ↔
      ∃ v : Fin N, x = decNode N v ∧ G.arena.owner v = false := by
  unfold FriedmannStochastic.Decision
  rcases vertex_cases x with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl
  · constructor
    · rintro ⟨_, _, hrole⟩
      rw [stochGame_role_decNode] at hrole
      refine ⟨v, rfl, ?_⟩
      cases hown : G.arena.owner v
      · rfl
      · rw [hown] at hrole; revert hrole; decide
    · rintro ⟨w, hw, hown⟩
      cases decNode_inj.mp hw
      refine ⟨decNode_ne_winNode v, decNode_ne_loseNode v, ?_⟩
      rw [stochGame_role_decNode, hown]
      rfl
  · constructor
    · rintro ⟨_, _, hrole⟩
      rw [stochGame_role_randNode] at hrole
      exact False.elim (by revert hrole; decide)
    · rintro ⟨w, hw, _⟩
      exact False.elim (decNode_ne_randNode w v hw.symm)
  · constructor
    · rintro ⟨h, _⟩; exact False.elim (h rfl)
    · rintro ⟨w, hw, _⟩; exact False.elim (decNode_ne_winNode w hw.symm)
  · constructor
    · rintro ⟨_, h, _⟩; exact False.elim (h rfl)
    · rintro ⟨w, hw, _⟩; exact False.elim (decNode_ne_loseNode w hw.symm)

lemma decision_one_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (x : Fin (2 * N + 2)) :
    FriedmannStochastic.Decision (stochGame hN G) 1 x ↔
      ∃ v : Fin N, x = decNode N v ∧ G.arena.owner v = true := by
  unfold FriedmannStochastic.Decision
  rcases vertex_cases x with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl
  · constructor
    · rintro ⟨_, _, hrole⟩
      rw [stochGame_role_decNode] at hrole
      refine ⟨v, rfl, ?_⟩
      cases hown : G.arena.owner v
      · rw [hown] at hrole; exact False.elim (by revert hrole; decide)
      · rfl
    · rintro ⟨w, hw, hown⟩
      cases decNode_inj.mp hw
      refine ⟨decNode_ne_winNode v, decNode_ne_loseNode v, ?_⟩
      rw [stochGame_role_decNode, hown]
      rfl
  · constructor
    · rintro ⟨_, _, hrole⟩
      rw [stochGame_role_randNode] at hrole
      exact False.elim (by revert hrole; decide)
    · rintro ⟨w, hw, _⟩
      exact False.elim (decNode_ne_randNode w v hw.symm)
  · constructor
    · rintro ⟨h, _⟩; exact False.elim (h rfl)
    · rintro ⟨w, hw, _⟩; exact False.elim (decNode_ne_winNode w hw.symm)
  · constructor
    · rintro ⟨_, h, _⟩; exact False.elim (h rfl)
    · rintro ⟨w, hw, _⟩; exact False.elim (decNode_ne_loseNode w hw.symm)

lemma decision_two_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (x : Fin (2 * N + 2)) :
    FriedmannStochastic.Decision (stochGame hN G) 2 x ↔
      ∃ v : Fin N, x = randNode N v := by
  unfold FriedmannStochastic.Decision
  rcases vertex_cases x with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl
  · constructor
    · rintro ⟨_, _, hrole⟩
      rw [stochGame_role_decNode] at hrole
      cases hown : G.arena.owner v <;>
        (rw [hown] at hrole; exact False.elim (by revert hrole; decide))
    · rintro ⟨w, hw⟩
      exact False.elim (decNode_ne_randNode v w hw)
  · constructor
    · intro _
      exact ⟨v, rfl⟩
    · intro _
      exact ⟨randNode_ne_winNode v, randNode_ne_loseNode v, stochGame_role_randNode hN G v⟩
  · constructor
    · rintro ⟨h, _⟩; exact False.elim (h rfl)
    · rintro ⟨w, hw⟩; exact False.elim (randNode_ne_winNode w hw.symm)
  · constructor
    · rintro ⟨_, h, _⟩; exact False.elim (h rfl)
    · rintro ⟨w, hw⟩; exact False.elim (randNode_ne_loseNode w hw.symm)

/-! ### Part 5: Well-Formedness and Edge Count of `stochGame` -/

lemma transition_randNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (σ' τ' : Fin (2 * N + 2) → Fin (2 * N + 2)) (v : Fin N) (y : Fin (2 * N + 2)) :
    FriedmannStochastic.transition (stochGame hN G) σ' τ' (randNode N v) y =
      (stochGame hN G).probability (randNode N v) y := by
  unfold FriedmannStochastic.transition
  have hterm : ¬ (randNode N v = (stochGame hN G).win ∨ randNode N v = (stochGame hN G).lose) := by
    rintro (h | h)
    · exact randNode_ne_winNode v h
    · exact randNode_ne_loseNode v h
  have hrole := stochGame_role_randNode hN G v
  rw [if_neg hterm, if_neg (by rw [hrole]; decide), if_neg (by rw [hrole]; decide)]

lemma transition_randNode_winNode_pos {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    (σ' τ' : Fin (2 * N + 2) → Fin (2 * N + 2)) (v : Fin N) :
    0 < FriedmannStochastic.transition (stochGame hN G) σ' τ' (randNode N v) (winNode N) := by
  rw [transition_randNode, stochGame_probability_randNode]
  rw [if_neg (decNode_ne_winNode v).symm, if_pos rfl, if_neg (winNode_ne_loseNode N)]
  simp only [zero_add, add_zero]
  exact mul_pos (sub_pos.mpr hG.2.2) (alpha_pos hN G v)

lemma stochGame_wellFormed {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) :
    FriedmannStochastic.WellFormed (stochGame hN G) := by
  refine ⟨winNode_ne_loseNode N, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hxwin hxlose
    rcases vertex_cases x with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl
    · rcases hG.1 v with ⟨w, hw⟩
      exact ⟨randNode N w, (stochGame_edge_decNode hN G v _).mpr ⟨w, rfl, hw⟩⟩
    · exact ⟨winNode N, (stochGame_edge_randNode hN G v _).mpr (Or.inr (Or.inl rfl))⟩
    · exact False.elim (hxwin rfl)
    · exact False.elim (hxlose rfl)
  · intro y
    exact ⟨stochGame_edge_winNode hN G y, stochGame_edge_loseNode hN G y⟩
  · intro x y hx
    rcases (decision_two_iff hN G x).mp hx with ⟨v, rfl⟩
    rw [stochGame_probability_randNode]
    constructor
    · have hβ0 : 0 ≤ G.discount := le_of_lt hG.2.1
      have hβ1 : 0 ≤ 1 - G.discount := le_of_lt (sub_pos.mpr hG.2.2)
      have hα0 : 0 ≤ alpha hN G v := le_of_lt (alpha_pos hN G v)
      have hα1 : 0 ≤ 1 - alpha hN G v := le_of_lt (one_sub_alpha_pos hN G v)
      split_ifs <;> positivity
    · intro hne
      rw [stochGame_edge_randNode] at hne
      push Not at hne
      rcases hne with ⟨h1, h2, h3⟩
      rw [if_neg h1, if_neg h2, if_neg h3]
      ring
  · intro x hx
    rcases (decision_two_iff hN G x).mp hx with ⟨v, rfl⟩
    simp only [stochGame_probability_randNode, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  · intro σ' τ' hσ' hτ' x
    have hrand : ∀ v : Fin N,
        Relation.ReflTransGen
          (fun a b => 0 < FriedmannStochastic.transition (stochGame hN G) σ' τ' a b)
          (randNode N v) (winNode N) :=
      fun v => Relation.ReflTransGen.single (transition_randNode_winNode_pos hN G hG σ' τ' v)
    rcases vertex_cases x with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl
    · left
      have hterm : ¬ (decNode N v = (stochGame hN G).win ∨ decNode N v = (stochGame hN G).lose) := by
        rintro (h | h)
        · exact decNode_ne_winNode v h
        · exact decNode_ne_loseNode v h
      cases hown : G.arena.owner v
      · have hdec : FriedmannStochastic.Decision (stochGame hN G) 0 (decNode N v) :=
          (decision_zero_iff hN G (decNode N v)).mpr ⟨v, rfl, hown⟩
        rcases (stochGame_edge_decNode hN G v (σ' (decNode N v))).mp (hσ' (decNode N v) hdec) with
          ⟨w, hw, _⟩
        have hstep : 0 < FriedmannStochastic.transition (stochGame hN G) σ' τ'
            (decNode N v) (randNode N w) := by
          unfold FriedmannStochastic.transition
          rw [if_neg hterm, stochGame_role_decNode, hown]
          simp only [↓reduceIte, hw]
          exact zero_lt_one
        exact Relation.ReflTransGen.head hstep (hrand w)
      · have hdec : FriedmannStochastic.Decision (stochGame hN G) 1 (decNode N v) :=
          (decision_one_iff hN G (decNode N v)).mpr ⟨v, rfl, hown⟩
        rcases (stochGame_edge_decNode hN G v (τ' (decNode N v))).mp (hτ' (decNode N v) hdec) with
          ⟨w, hw, _⟩
        have hstep : 0 < FriedmannStochastic.transition (stochGame hN G) σ' τ'
            (decNode N v) (randNode N w) := by
          unfold FriedmannStochastic.transition
          rw [if_neg hterm, stochGame_role_decNode, hown]
          simp only [reduceCtorEq, ↓reduceIte, hw]
          exact zero_lt_one
        exact Relation.ReflTransGen.head hstep (hrand w)
    · exact Or.inl (hrand v)
    · exact Or.inl Relation.ReflTransGen.refl
    · exact Or.inr Relation.ReflTransGen.refl

lemma card_le_arena_edgeCount {N : ℕ} (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) :
    N ≤ edgeCount G.arena := by
  classical
  let f : Fin N → Fin N × Fin N := fun v => (v, Classical.choose (hG.1 v))
  have hinj : Function.Injective f := fun u v h => congrArg Prod.fst h
  have hsub : Finset.univ.image f ⊆
      Finset.univ.filter (fun e : Fin N × Fin N => G.arena.edge e.1 e.2) := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨v, _, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Classical.choose_spec (hG.1 v)⟩
  calc N = (Finset.univ : Finset (Fin N)).card := (Fintype.card_fin N).symm
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ edgeCount G.arena := Finset.card_le_card hsub

lemma stochGame_edgeCount_le {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) :
    FriedmannStochastic.edgeCount (stochGame hN G) ≤ 4 * edgeCount G.arena := by
  classical
  let E_arena := Finset.univ.filter (fun e : Fin N × Fin N => G.arena.edge e.1 e.2)
  let S_dec := E_arena.image (fun e => (decNode N e.1, randNode N e.2))
  let S_r1 := (Finset.univ : Finset (Fin N)).image (fun v => (randNode N v, decNode N v))
  let S_r2 := (Finset.univ : Finset (Fin N)).image (fun v => (randNode N v, winNode N))
  let S_r3 := (Finset.univ : Finset (Fin N)).image (fun v => (randNode N v, loseNode N))
  have hsub : Finset.univ.filter (fun e : Fin (2 * N + 2) × Fin (2 * N + 2) =>
      (stochGame hN G).edge e.1 e.2) ⊆ S_dec ∪ (S_r1 ∪ (S_r2 ∪ S_r3)) := by
    rintro ⟨x, y⟩ he
    have hedge : (stochGame hN G).edge x y := (Finset.mem_filter.mp he).2
    rcases vertex_cases x with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl
    · rcases (stochGame_edge_decNode hN G v y).mp hedge with ⟨w, rfl, hvw⟩
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(v, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw⟩, rfl⟩
    · apply Finset.mem_union_right
      rcases (stochGame_edge_randNode hN G v y).mp hedge with rfl | rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩))
    · exact False.elim (stochGame_edge_winNode hN G y hedge)
    · exact False.elim (stochGame_edge_loseNode hN G y hedge)
  have hcard1 : FriedmannStochastic.edgeCount (stochGame hN G) ≤
      (S_dec ∪ (S_r1 ∪ (S_r2 ∪ S_r3))).card := Finset.card_le_card hsub
  have hcard2 : (S_dec ∪ (S_r1 ∪ (S_r2 ∪ S_r3))).card ≤
      S_dec.card + S_r1.card + S_r2.card + S_r3.card := by
    have u1 := Finset.card_union_le S_dec (S_r1 ∪ (S_r2 ∪ S_r3))
    have u2 := Finset.card_union_le S_r1 (S_r2 ∪ S_r3)
    have u3 := Finset.card_union_le S_r2 S_r3
    omega
  have hc_dec : S_dec.card ≤ edgeCount G.arena := Finset.card_image_le
  have hc_r1 : S_r1.card ≤ N := by
    simpa [Fintype.card_fin] using (Finset.card_image_le : S_r1.card ≤ Finset.univ.card)
  have hc_r2 : S_r2.card ≤ N := by
    simpa [Fintype.card_fin] using (Finset.card_image_le : S_r2.card ≤ Finset.univ.card)
  have hc_r3 : S_r3.card ≤ N := by
    simpa [Fintype.card_fin] using (Finset.card_image_le : S_r3.card ≤ Finset.univ.card)
  have hN_le := card_le_arena_edgeCount G hG
  omega

/-! ### Part 6: Strategy Lifting, Projection, and `playValue` Affine Identity -/

def proj {N : ℕ} (hN : 0 < N) (σ' : Fin (2 * N + 2) → Fin (2 * N + 2)) (v : Fin N) : Fin N :=
  unrand hN (σ' (decNode N v))

def lift (N : ℕ) (σ : Fin N → Fin N) (x : Fin (2 * N + 2)) : Fin (2 * N + 2) :=
  if h : x.val < N then randNode N (σ ⟨x.val, h⟩) else x

@[simp]
lemma lift_decNode {N : ℕ} (σ : Fin N → Fin N) (v : Fin N) :
    lift N σ (decNode N v) = randNode N (σ v) := by
  unfold lift decNode
  exact dif_pos v.isLt

@[simp]
lemma proj_lift {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin N) :
    proj hN (lift N σ) = σ := by
  ext v
  simp [proj]

lemma legal_zero_lift {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    {σ : Fin N → Fin N} (hσ : Legal G.arena false σ) :
    FriedmannStochastic.Legal (stochGame hN G) 0 (lift N σ) := by
  intro x hx
  rcases (decision_zero_iff hN G x).mp hx with ⟨v, rfl, hv⟩
  rw [lift_decNode, stochGame_edge_decNode_randNode]
  exact hσ v hv

lemma legal_one_lift {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    {τ : Fin N → Fin N} (hτ : Legal G.arena true τ) :
    FriedmannStochastic.Legal (stochGame hN G) 1 (lift N τ) := by
  intro x hx
  rcases (decision_one_iff hN G x).mp hx with ⟨v, rfl, hv⟩
  rw [lift_decNode, stochGame_edge_decNode_randNode]
  exact hτ v hv

lemma apply_decNode_of_legal_zero {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    {v : Fin N} (hv : G.arena.owner v = false) :
    σ' (decNode N v) = randNode N (proj hN σ' v) ∧ G.arena.edge v (proj hN σ' v) := by
  have hdec : FriedmannStochastic.Decision (stochGame hN G) 0 (decNode N v) :=
    (decision_zero_iff hN G (decNode N v)).mpr ⟨v, rfl, hv⟩
  rcases (stochGame_edge_decNode hN G v (σ' (decNode N v))).mp (hσ' (decNode N v) hdec) with
    ⟨w, hw, hedge⟩
  have hproj : proj hN σ' v = w := by
    unfold proj
    rw [hw, unrand_randNode]
  rw [hproj]
  exact ⟨hw, hedge⟩

lemma legal_false_proj {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    Legal G.arena false (proj hN σ') :=
  fun _ hv => (apply_decNode_of_legal_zero hN G hσ' hv).2

lemma apply_decNode_of_legal_one {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    {τ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hτ' : FriedmannStochastic.Legal (stochGame hN G) 1 τ')
    {v : Fin N} (hv : G.arena.owner v = true) :
    τ' (decNode N v) = randNode N (proj hN τ' v) ∧ G.arena.edge v (proj hN τ' v) := by
  have hdec : FriedmannStochastic.Decision (stochGame hN G) 1 (decNode N v) :=
    (decision_one_iff hN G (decNode N v)).mpr ⟨v, rfl, hv⟩
  rcases (stochGame_edge_decNode hN G v (τ' (decNode N v))).mp (hτ' (decNode N v) hdec) with
    ⟨w, hw, hedge⟩
  have hproj : proj hN τ' v = w := by
    unfold proj
    rw [hw, unrand_randNode]
  rw [hproj]
  exact ⟨hw, hedge⟩

lemma legal_true_proj {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    {τ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hτ' : FriedmannStochastic.Legal (stochGame hN G) 1 τ') :
    Legal G.arena true (proj hN τ') :=
  fun _ hv => (apply_decNode_of_legal_one hN G hτ' hv).2

noncomputable def scaleRand {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) : ℚ :=
  (1 - G.discount) / span hN G

noncomputable def shiftRand {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) : ℚ :=
  -lowerBound hN G / span hN G

noncomputable def scaleDec {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) : ℚ :=
  scaleRand hN G / G.discount

noncomputable def shiftDec {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N)) (v : Fin N) : ℚ :=
  (shiftRand hN G - (1 - G.discount) * alpha hN G v) / G.discount

lemma scaleRand_pos {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) :
    0 < scaleRand hN G :=
  div_pos (sub_pos.mpr hG.2.2) (span_pos hN G)

lemma scaleDec_pos {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) :
    0 < scaleDec hN G :=
  div_pos (scaleRand_pos hN G hG) hG.2.1

lemma playValue_decNode_eq_randNode_step {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' τ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    (hτ' : FriedmannStochastic.Legal (stochGame hN G) 1 τ')
    (v : Fin N) :
    FriedmannStochastic.playValue (stochGame hN G) σ' τ' (decNode N v) =
      FriedmannStochastic.playValue (stochGame hN G) σ' τ'
        (randNode N (if G.arena.owner v = false then proj hN σ' v else proj hN τ' v)) := by
  have habs := FriedmannStochastic.absorption_values (stochGame hN G)
    (stochGame_wellFormed hN G hG) σ' τ' hσ' hτ'
  rw [habs.2.2.2.2 (decNode N v) (decNode_ne_winNode v) (decNode_ne_loseNode v)]
  have hterm : ¬ (decNode N v = (stochGame hN G).win ∨ decNode N v = (stochGame hN G).lose) := by
    rintro (h | h)
    · exact decNode_ne_winNode v h
    · exact decNode_ne_loseNode v h
  cases hown : G.arena.owner v
  · have hstep := (apply_decNode_of_legal_zero hN G hσ' hown).1
    have hcongr : ∀ w, FriedmannStochastic.transition (stochGame hN G) σ' τ' (decNode N v) w =
        if randNode N (proj hN σ' v) = w then 1 else 0 := by
      intro w
      unfold FriedmannStochastic.transition
      rw [if_neg hterm, stochGame_role_decNode, hown]
      simp only [↓reduceIte, hstep]
    simp [hcongr]
  · have hstep := (apply_decNode_of_legal_one hN G hτ' hown).1
    have hcongr : ∀ w, FriedmannStochastic.transition (stochGame hN G) σ' τ' (decNode N v) w =
        if randNode N (proj hN τ' v) = w then 1 else 0 := by
      intro w
      unfold FriedmannStochastic.transition
      rw [if_neg hterm, stochGame_role_decNode, hown]
      simp only [reduceCtorEq, ↓reduceIte, hstep]
      rfl
    simp [hcongr]

lemma playValue_randNode_eq_decNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' τ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    (hτ' : FriedmannStochastic.Legal (stochGame hN G) 1 τ')
    (v : Fin N) :
    FriedmannStochastic.playValue (stochGame hN G) σ' τ' (randNode N v) =
      G.discount * FriedmannStochastic.playValue (stochGame hN G) σ' τ' (decNode N v) +
      (1 - G.discount) * alpha hN G v := by
  have habs := FriedmannStochastic.absorption_values (stochGame hN G)
    (stochGame_wellFormed hN G hG) σ' τ' hσ' hτ'
  rw [habs.2.2.2.2 (randNode N v) (randNode_ne_winNode v) (randNode_ne_loseNode v)]
  simp only [transition_randNode, stochGame_probability_randNode, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hwin : FriedmannStochastic.playValue (stochGame hN G) σ' τ' (winNode N) = 1 := habs.2.1
  have hlose : FriedmannStochastic.playValue (stochGame hN G) σ' τ' (loseNode N) = 0 := habs.2.2.1
  rw [hwin, hlose]
  ring

lemma playValue_randNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' τ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    (hτ' : FriedmannStochastic.Legal (stochGame hN G) 1 τ')
    (v : Fin N) :
    FriedmannStochastic.playValue (stochGame hN G) σ' τ' (randNode N v) =
      scaleRand hN G * FriedmannDiscounted.playValue G (proj hN σ') (proj hN τ') v +
      shiftRand hN G := by
  set y := FriedmannStochastic.playValue (stochGame hN G) σ' τ'
  let x_cand : Fin N → ℚ := fun u =>
    (span hN G / (1 - G.discount)) * y (randNode N u) + lowerBound hN G / (1 - G.discount)
  have h1mβ : 1 - G.discount ≠ 0 := ne_of_gt (sub_pos.mpr hG.2.2)
  have hspan : span hN G ≠ 0 := ne_of_gt (span_pos hN G)
  have hbell : ∀ u, x_cand u = G.reward u + G.discount *
      x_cand (if G.arena.owner u = false then proj hN σ' u else proj hN τ' u) := by
    intro u
    have hy1 := playValue_randNode_eq_decNode hN G hG hσ' hτ' u
    have hy2 := playValue_decNode_eq_randNode_step hN G hG hσ' hτ' u
    dsimp [x_cand, y] at hy1 hy2 ⊢
    rw [hy1, hy2]
    unfold alpha
    field_simp [h1mβ, hspan]
    ring
  have hx_eq : x_cand = FriedmannDiscounted.playValue G (proj hN σ') (proj hN τ') :=
    (FriedmannDiscounted.discounted_bellman G hG (proj hN σ') (proj hN τ')).2 x_cand hbell
  have hxv : FriedmannDiscounted.playValue G (proj hN σ') (proj hN τ') v = x_cand v :=
    congrFun hx_eq.symm v
  rw [hxv]
  dsimp [x_cand, scaleRand, shiftRand]
  field_simp [h1mβ, hspan]
  ring

lemma playValue_decNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' τ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    (hτ' : FriedmannStochastic.Legal (stochGame hN G) 1 τ')
    (v : Fin N) :
    FriedmannStochastic.playValue (stochGame hN G) σ' τ' (decNode N v) =
      scaleDec hN G * FriedmannDiscounted.playValue G (proj hN σ') (proj hN τ') v +
      shiftDec hN G v := by
  have hy1 := playValue_randNode_eq_decNode hN G hG hσ' hτ' v
  have hy2 := playValue_randNode hN G hG hσ' hτ' v
  have hβ : G.discount ≠ 0 := ne_of_gt hG.2.1
  unfold scaleDec shiftDec
  field_simp [hβ]
  linarith

/-! ### Part 7: Affine Correspondence of `FriedmannScalar.value` -/

lemma stoch_value_randNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    (v : Fin N) :
    FriedmannScalar.value (FriedmannStochastic.model (stochGame hN G)) σ' (randNode N v) =
      scaleRand hN G * FriedmannScalar.value (FriedmannDiscounted.model G) (proj hN σ') v +
      shiftRand hN G := by
  rcases discounted_value_spec G hG (proj hN σ') v with ⟨⟨τ_min, hτ_min, hmin_eq⟩, hmin_le⟩
  apply scalar_value_eq_of_isMin (FriedmannStochastic.model (stochGame hN G)) σ' (randNode N v)
  · refine ⟨lift N τ_min, legal_one_lift hN G hτ_min, ?_⟩
    change FriedmannStochastic.playValue (stochGame hN G) σ' (lift N τ_min) (randNode N v) = _
    rw [playValue_randNode hN G hG hσ' (legal_one_lift hN G hτ_min) v, proj_lift, hmin_eq]
  · intro τ' hτ'
    change _ ≤ FriedmannStochastic.playValue (stochGame hN G) σ' τ' (randNode N v)
    rw [playValue_randNode hN G hG hσ' hτ' v]
    have hle := hmin_le (proj hN τ') (legal_true_proj hN G hτ')
    have hpos := le_of_lt (scaleRand_pos hN G hG)
    linarith [mul_le_mul_of_nonneg_left hle hpos]

lemma stoch_value_decNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    (v : Fin N) :
    FriedmannScalar.value (FriedmannStochastic.model (stochGame hN G)) σ' (decNode N v) =
      scaleDec hN G * FriedmannScalar.value (FriedmannDiscounted.model G) (proj hN σ') v +
      shiftDec hN G v := by
  rcases discounted_value_spec G hG (proj hN σ') v with ⟨⟨τ_min, hτ_min, hmin_eq⟩, hmin_le⟩
  apply scalar_value_eq_of_isMin (FriedmannStochastic.model (stochGame hN G)) σ' (decNode N v)
  · refine ⟨lift N τ_min, legal_one_lift hN G hτ_min, ?_⟩
    change FriedmannStochastic.playValue (stochGame hN G) σ' (lift N τ_min) (decNode N v) = _
    rw [playValue_decNode hN G hG hσ' (legal_one_lift hN G hτ_min) v, proj_lift, hmin_eq]
  · intro τ' hτ'
    change _ ≤ FriedmannStochastic.playValue (stochGame hN G) σ' τ' (decNode N v)
    rw [playValue_decNode hN G hG hσ' hτ' v]
    have hle := hmin_le (proj hN τ') (legal_true_proj hN G hτ')
    have hpos := le_of_lt (scaleDec_pos hN G hG)
    linarith [mul_le_mul_of_nonneg_left hle hpos]

lemma stoch_value_winNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    FriedmannScalar.value (FriedmannStochastic.model (stochGame hN G)) σ' (winNode N) = 1 := by
  rcases exists_legal_true G hG with ⟨τ₀, hτ₀⟩
  apply scalar_value_eq_of_isMin (FriedmannStochastic.model (stochGame hN G)) σ' (winNode N)
  · refine ⟨lift N τ₀, legal_one_lift hN G hτ₀, ?_⟩
    exact (FriedmannStochastic.absorption_values (stochGame hN G)
      (stochGame_wellFormed hN G hG) σ' (lift N τ₀) hσ' (legal_one_lift hN G hτ₀)).2.1
  · intro τ' hτ'
    have h := (FriedmannStochastic.absorption_values (stochGame hN G)
      (stochGame_wellFormed hN G hG) σ' τ' hσ' hτ').2.1
    exact le_of_eq h.symm

lemma stoch_value_loseNode {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    FriedmannScalar.value (FriedmannStochastic.model (stochGame hN G)) σ' (loseNode N) = 0 := by
  rcases exists_legal_true G hG with ⟨τ₀, hτ₀⟩
  apply scalar_value_eq_of_isMin (FriedmannStochastic.model (stochGame hN G)) σ' (loseNode N)
  · refine ⟨lift N τ₀, legal_one_lift hN G hτ₀, ?_⟩
    exact (FriedmannStochastic.absorption_values (stochGame hN G)
      (stochGame_wellFormed hN G hG) σ' (lift N τ₀) hσ' (legal_one_lift hN G hτ₀)).2.2.1
  · intro τ' hτ'
    have h := (FriedmannStochastic.absorption_values (stochGame hN G)
      (stochGame_wellFormed hN G hG) σ' τ' hσ' hτ').2.2.1
    exact le_of_eq h.symm

/-! ### Part 8: Policy Iteration Equivalence -/

lemma stoch_value_randNode_lt_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    (u w : Fin N) :
    FriedmannScalar.value (FriedmannStochastic.model (stochGame hN G)) σ' (randNode N u) <
      FriedmannScalar.value (FriedmannStochastic.model (stochGame hN G)) σ' (randNode N w) ↔
    FriedmannScalar.value (FriedmannDiscounted.model G) (proj hN σ') u <
      FriedmannScalar.value (FriedmannDiscounted.model G) (proj hN σ') w := by
  rw [stoch_value_randNode hN G hG hσ' u, stoch_value_randNode hN G hG hσ' w]
  have hpos := scaleRand_pos hN G hG
  constructor <;> intro h
  · nlinarith
  · linarith [mul_lt_mul_of_pos_left h hpos]

lemma stoch_value_randNode_le_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ')
    (u w : Fin N) :
    FriedmannScalar.value (FriedmannStochastic.model (stochGame hN G)) σ' (randNode N u) ≤
      FriedmannScalar.value (FriedmannStochastic.model (stochGame hN G)) σ' (randNode N w) ↔
    FriedmannScalar.value (FriedmannDiscounted.model G) (proj hN σ') u ≤
      FriedmannScalar.value (FriedmannDiscounted.model G) (proj hN σ') w := by
  rw [stoch_value_randNode hN G hG hσ' u, stoch_value_randNode hN G hG hσ' w]
  have hpos := scaleRand_pos hN G hG
  constructor <;> intro h
  · nlinarith
  · linarith [mul_le_mul_of_nonneg_left h (le_of_lt hpos)]

lemma improvable_stoch_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    FriedmannScalar.Improvable (FriedmannStochastic.model (stochGame hN G)) σ' ↔
      FriedmannScalar.Improvable (FriedmannDiscounted.model G) (proj hN σ') := by
  constructor
  · rintro ⟨x, y, hx, hxy, hlt⟩
    rcases (decision_zero_iff hN G x).mp hx with ⟨v, rfl, hv⟩
    rcases (stochGame_edge_decNode hN G v y).mp hxy with ⟨w, rfl, hvw⟩
    rw [(apply_decNode_of_legal_zero hN G hσ' hv).1,
      stoch_value_randNode_lt_iff hN G hG hσ'] at hlt
    exact ⟨v, w, hv, hvw, hlt⟩
  · rintro ⟨v, w, hv, hvw, hlt⟩
    refine ⟨decNode N v, randNode N w,
      (decision_zero_iff hN G (decNode N v)).mpr ⟨v, rfl, hv⟩,
      (stochGame_edge_decNode_randNode hN G v w).mpr hvw, ?_⟩
    rw [(apply_decNode_of_legal_zero hN G hσ' hv).1,
      stoch_value_randNode_lt_iff hN G hG hσ']
    exact hlt

lemma allowed_stoch_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' σ'' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    FriedmannScalar.Allowed (FriedmannStochastic.model (stochGame hN G)) σ' σ'' ↔
      FriedmannStochastic.Legal (stochGame hN G) 0 σ'' ∧
        FriedmannScalar.Allowed (FriedmannDiscounted.model G) (proj hN σ') (proj hN σ'') := by
  constructor
  · rintro ⟨hσ'', hall⟩
    refine ⟨hσ'', legal_false_proj hN G hσ'', ?_⟩
    intro v hv
    have hdec : FriedmannStochastic.Decision (stochGame hN G) 0 (decNode N v) :=
      (decision_zero_iff hN G (decNode N v)).mpr ⟨v, rfl, hv⟩
    have hle := hall (decNode N v) hdec
    rw [(apply_decNode_of_legal_zero hN G hσ' hv).1,
      (apply_decNode_of_legal_zero hN G hσ'' hv).1,
      stoch_value_randNode_le_iff hN G hG hσ'] at hle
    exact hle
  · rintro ⟨hσ'', _, hall⟩
    refine ⟨hσ'', ?_⟩
    intro x hx
    rcases (decision_zero_iff hN G x).mp hx with ⟨v, rfl, hv⟩
    rw [(apply_decNode_of_legal_zero hN G hσ' hv).1,
      (apply_decNode_of_legal_zero hN G hσ'' hv).1,
      stoch_value_randNode_le_iff hN G hG hσ']
    exact hall v hv

lemma improvement_stoch_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' σ'' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    FriedmannScalar.Improvement (FriedmannStochastic.model (stochGame hN G)) σ' σ'' ↔
      FriedmannStochastic.Legal (stochGame hN G) 0 σ'' ∧
        FriedmannScalar.Improvement (FriedmannDiscounted.model G) (proj hN σ') (proj hN σ'') := by
  unfold FriedmannScalar.Improvement
  rw [allowed_stoch_iff hN G hG hσ', improvable_stoch_iff hN G hG hσ']
  constructor
  · rintro ⟨⟨hσ'', hall⟩, himp⟩
    refine ⟨hσ'', hall, fun h => ?_⟩
    rcases himp h with ⟨x, hx, hlt⟩
    rcases (decision_zero_iff hN G x).mp hx with ⟨v, rfl, hv⟩
    rw [(apply_decNode_of_legal_zero hN G hσ' hv).1,
      (apply_decNode_of_legal_zero hN G hσ'' hv).1,
      stoch_value_randNode_lt_iff hN G hG hσ'] at hlt
    exact ⟨v, hv, hlt⟩
  · rintro ⟨hσ'', hall, himp⟩
    refine ⟨⟨hσ'', hall⟩, fun h => ?_⟩
    rcases himp h with ⟨v, hv, hlt⟩
    refine ⟨decNode N v, (decision_zero_iff hN G (decNode N v)).mpr ⟨v, rfl, hv⟩, ?_⟩
    rw [(apply_decNode_of_legal_zero hN G hσ' hv).1,
      (apply_decNode_of_legal_zero hN G hσ'' hv).1,
      stoch_value_randNode_lt_iff hN G hG hσ']
    exact hlt

lemma localStep_stoch_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' σ'' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    FriedmannScalar.LocalStep (FriedmannStochastic.model (stochGame hN G)) σ' σ'' ↔
      FriedmannStochastic.Legal (stochGame hN G) 0 σ'' ∧
        FriedmannScalar.LocalStep (FriedmannDiscounted.model G) (proj hN σ') (proj hN σ'') := by
  unfold FriedmannScalar.LocalStep
  rw [improvement_stoch_iff hN G hG hσ']
  constructor
  · rintro ⟨⟨hσ'', himp⟩, hloc⟩
    refine ⟨hσ'', himp, ?_⟩
    intro v w hv hvw
    have hle := hloc (decNode N v) (randNode N w)
      ((decision_zero_iff hN G (decNode N v)).mpr ⟨v, rfl, hv⟩)
      ((stochGame_edge_decNode_randNode hN G v w).mpr hvw)
    rw [(apply_decNode_of_legal_zero hN G hσ'' hv).1,
      stoch_value_randNode_le_iff hN G hG hσ'] at hle
    exact hle
  · rintro ⟨hσ'', himp, hloc⟩
    refine ⟨⟨hσ'', himp⟩, ?_⟩
    intro x y hx hxy
    rcases (decision_zero_iff hN G x).mp hx with ⟨v, rfl, hv⟩
    rcases (stochGame_edge_decNode hN G v y).mp hxy with ⟨w, rfl, hvw⟩
    rw [(apply_decNode_of_legal_zero hN G hσ'' hv).1,
      stoch_value_randNode_le_iff hN G hG hσ']
    exact hloc v w hv hvw

lemma globalStep_stoch_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G)
    {σ' σ'' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    FriedmannScalar.GlobalStep (FriedmannStochastic.model (stochGame hN G)) σ' σ'' ↔
      FriedmannStochastic.Legal (stochGame hN G) 0 σ'' ∧
        FriedmannScalar.GlobalStep (FriedmannDiscounted.model G) (proj hN σ') (proj hN σ'') := by
  unfold FriedmannScalar.GlobalStep
  rw [improvement_stoch_iff hN G hG hσ']
  constructor
  · rintro ⟨⟨hσ'', himp⟩, hglob⟩
    refine ⟨hσ'', himp, ?_⟩
    intro ρ hρ v
    have hρ' : FriedmannScalar.Allowed (FriedmannStochastic.model (stochGame hN G))
        σ' (lift N ρ) := by
      rw [allowed_stoch_iff hN G hG hσ', proj_lift]
      exact ⟨legal_zero_lift hN G hρ.1, hρ⟩
    have hle := hglob (lift N ρ) hρ' (randNode N v)
    rw [stoch_value_randNode hN G hG (legal_zero_lift hN G hρ.1) v,
      stoch_value_randNode hN G hG hσ'' v, proj_lift] at hle
    have hpos := scaleRand_pos hN G hG
    nlinarith
  · rintro ⟨hσ'', himp, hglob⟩
    refine ⟨⟨hσ'', himp⟩, ?_⟩
    intro ρ' hρ' x
    rcases (allowed_stoch_iff hN G hG hσ').mp hρ' with ⟨hρ'_leg, hρ⟩
    rcases vertex_cases x with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl
    · rw [stoch_value_decNode hN G hG hρ'_leg v, stoch_value_decNode hN G hG hσ'' v]
      have hle := hglob (proj hN ρ') hρ v
      have hpos := le_of_lt (scaleDec_pos hN G hG)
      linarith [mul_le_mul_of_nonneg_left hle hpos]
    · rw [stoch_value_randNode hN G hG hρ'_leg v, stoch_value_randNode hN G hG hσ'' v]
      have hle := hglob (proj hN ρ') hρ v
      have hpos := le_of_lt (scaleRand_pos hN G hG)
      linarith [mul_le_mul_of_nonneg_left hle hpos]
    · rw [stoch_value_winNode hN G hG hρ'_leg, stoch_value_winNode hN G hG hσ'']
    · rw [stoch_value_loseNode hN G hG hρ'_leg, stoch_value_loseNode hN G hG hσ'']

lemma rule_stoch_iff {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) (global : Bool)
    {σ' σ'' : Fin (2 * N + 2) → Fin (2 * N + 2)}
    (hσ' : FriedmannStochastic.Legal (stochGame hN G) 0 σ') :
    FriedmannScalar.rule (FriedmannStochastic.model (stochGame hN G)) global σ' σ'' ↔
      FriedmannStochastic.Legal (stochGame hN G) 0 σ'' ∧
        FriedmannScalar.rule (FriedmannDiscounted.model G) global (proj hN σ') (proj hN σ'') := by
  unfold FriedmannScalar.rule
  cases global
  · exact localStep_stoch_iff hN G hG hσ'
  · exact globalStep_stoch_iff hN G hG hσ'

lemma completeRun_lift {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) (global : Bool)
    (ι : Fin N → Fin N) (T : ℕ) (run : ℕ → (Fin N → Fin N))
    (hrun : FriedmannScalar.CompleteRun (FriedmannDiscounted.model G)
      (FriedmannScalar.rule (FriedmannDiscounted.model G) global) ι T run) :
    FriedmannScalar.CompleteRun (FriedmannStochastic.model (stochGame hN G))
      (FriedmannScalar.rule (FriedmannStochastic.model (stochGame hN G)) global)
      (lift N ι) T (fun t => lift N (run t)) := by
  rcases hrun with ⟨h0, hleg, hstep, hterm⟩
  refine ⟨by dsimp; rw [h0], ?_, ?_, ?_⟩
  · intro t ht
    exact legal_zero_lift hN G (hleg t ht)
  · intro t ht
    have hleg_t : FriedmannStochastic.Legal (stochGame hN G) 0 (lift N (run t)) :=
      legal_zero_lift hN G (hleg t (le_of_lt ht))
    have hleg_succ : FriedmannStochastic.Legal (stochGame hN G) 0 (lift N (run (t + 1))) :=
      legal_zero_lift hN G (hleg (t + 1) ht)
    rw [improvable_stoch_iff hN G hG hleg_t,
      rule_stoch_iff hN G hG global hleg_t, proj_lift, proj_lift]
    exact ⟨(hstep t ht).1, hleg_succ, (hstep t ht).2⟩
  · have hleg_T : FriedmannStochastic.Legal (stochGame hN G) 0 (lift N (run T)) :=
      legal_zero_lift hN G (hleg T le_rfl)
    rw [improvable_stoch_iff hN G hG hleg_T, proj_lift]
    exact hterm

lemma completeRun_proj {N : ℕ} (hN : 0 < N) (G : FriedmannDiscounted.Game (Fin N))
    (hG : FriedmannDiscounted.WellFormed G) (global : Bool)
    (ι : Fin N → Fin N) (T : ℕ) (run' : ℕ → (Fin (2 * N + 2) → Fin (2 * N + 2)))
    (hrun' : FriedmannScalar.CompleteRun (FriedmannStochastic.model (stochGame hN G))
      (FriedmannScalar.rule (FriedmannStochastic.model (stochGame hN G)) global)
      (lift N ι) T run') :
    FriedmannScalar.CompleteRun (FriedmannDiscounted.model G)
      (FriedmannScalar.rule (FriedmannDiscounted.model G) global)
      ι T (fun t => proj hN (run' t)) := by
  rcases hrun' with ⟨h0, hleg', hstep', hterm'⟩
  refine ⟨by dsimp; rw [h0, proj_lift], ?_, ?_, ?_⟩
  · intro t ht
    exact legal_false_proj hN G (hleg' t ht)
  · intro t ht
    have hleg_t := hleg' t (le_of_lt ht)
    rcases hstep' t ht with ⟨himp, hrule⟩
    rw [improvable_stoch_iff hN G hG hleg_t] at himp
    rw [rule_stoch_iff hN G hG global hleg_t] at hrule
    exact ⟨himp, hrule.2⟩
  · have hleg_T := hleg' T le_rfl
    rw [improvable_stoch_iff hN G hG hleg_T] at hterm'
    exact hterm'

theorem exponential_stochastic_of_discounted
    (h : FriedmannDiscounted.Exponential) : FriedmannStochastic.Exponential := by
  rcases h with ⟨C, hC, hExp⟩
  refine ⟨4 * C, by omega, ?_⟩
  intro global n hn
  rcases hExp global n hn with ⟨N, G, ι, hG, hedge, hHard⟩
  have h2n : 0 < 2 ^ n := Nat.two_pow_pos n
  have hN : 0 < N := pos_of_hardInstance h2n hHard
  refine ⟨2 * N + 2, stochGame hN G, lift N ι,
    stochGame_wellFormed hN G hG, ?_, ?_⟩
  · calc FriedmannStochastic.edgeCount (stochGame hN G)
      _ ≤ 4 * edgeCount G.arena := stochGame_edgeCount_le hN G hG
      _ ≤ 4 * (C * n) := Nat.mul_le_mul_left 4 hedge
      _ = 4 * C * n := (Nat.mul_assoc 4 C n).symm
  · rcases hHard with ⟨hι, ⟨T₀, run₀, hrun₀⟩, hbound⟩
    refine ⟨legal_zero_lift hN G hι,
      ⟨T₀, fun t => lift N (run₀ t), completeRun_lift hN G hG global ι T₀ run₀ hrun₀⟩, ?_⟩
    intro T run' hrun'
    exact hbound T (fun t => proj hN (run' t))
      (completeRun_proj hN G hG global ι T run' hrun')

theorem exponential_stochastic : FriedmannStochastic.Exponential :=
  exponential_stochastic_of_discounted exponential_payoff.1

end FriedmannParity

end Mod_stochastic

open FriedmannParity in
theorem solution : FriedmannStochastic.Exponential := by
  first
    | exact FriedmannParity.exponential_stochastic
    | (apply FriedmannParity.exponential_stochastic <;> assumption)
