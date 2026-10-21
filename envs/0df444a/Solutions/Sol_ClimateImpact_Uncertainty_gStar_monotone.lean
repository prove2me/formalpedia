-- Prove2me | solution 1 for ClimateImpact.Uncertainty.gStar_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:41:31.586994+00:00
-- url     : https://prove2.me/submissions/cd508cc8-1448-4ee6-8cfe-0da911ba4880

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint

set_option autoImplicit false
open Matrix ClimateImpact.Uncertainty

lemma clu2_beta_facts (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T) :
    0 ≤ ClimateImpact.Interaction.beta ρ T t ∧ 0 ≤ ClimateImpact.Interaction.betaC ρ T t ∧
      ClimateImpact.Interaction.beta ρ T t + ClimateImpact.Interaction.betaC ρ T t = 1 := by
  obtain ⟨ht0, htT⟩ := ht
  have hT1 : Real.exp (-(ρ * T)) < 1 := by
    have := Real.exp_lt_exp.2 (show -(ρ * T) < 0 by nlinarith)
    simpa using this
  have hden : 0 < 1 - Real.exp (-(ρ * T)) := by linarith
  have h1 : Real.exp (-(ρ * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have h2 : Real.exp (-(ρ * T)) ≤ Real.exp (-(ρ * t)) := by
    apply Real.exp_le_exp.2; nlinarith
  unfold ClimateImpact.Interaction.beta ClimateImpact.Interaction.betaC
  refine ⟨div_nonneg (by linarith) hden.le, div_nonneg (by linarith) hden.le, ?_⟩
  rw [← add_div]
  rw [div_eq_one_iff_eq hden.ne']
  ring

lemma clu2_q_nonneg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (θ : Fin n → ℝ) :
    0 ≤ quadForm S θ := by
  have hinv := hS.inv
  by_cases h : θ = 0
  · subst h
    simp [quadForm]
  · have := hinv.dotProduct_mulVec_pos h
    have e : star θ = θ := by ext i; simp
    rw [e] at this
    exact this.le

lemma clu2_D_pos (α ρ T t κ κc y : ℝ) (hα0 : 0 < α) (hρ : 0 < ρ) (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T) (hκ : 0 < κ) (hκc : 0 < κc) (hy : 0 < y) :
    0 < α * ClimateImpact.Interaction.beta ρ T t * κ * y + ClimateImpact.Interaction.betaC ρ T t * κc := by
  obtain ⟨hb, hbc, hsum⟩ := clu2_beta_facts ρ T t hρ hT ht
  rcases eq_or_lt_of_le hb with h | h
  · have : ClimateImpact.Interaction.betaC ρ T t = 1 := by linarith
    rw [← h, this]; nlinarith
  · have : 0 < α * ClimateImpact.Interaction.beta ρ T t * κ * y := by positivity
    nlinarith [mul_nonneg hbc hκc.le]

/-- The key monotonicity lemma, in terms of abstract data. -/
lemma clu2_mono_core {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hMsym : ∀ i j, M i j = M j i)
    (hMpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, v i * ∑ j, M i j * v j)
    (γ κ κ₀ A B : ℝ) (hγ : 0 < γ) (hκ : 0 < κ) (hA : 0 ≤ A) (c : Fin n → ℝ)
    (hD : ∀ y : ℝ, 0 < y → 0 < A * y + B)
    (h24 : ∀ i, ∀ y : ℝ, 0 < y →
      -(γ / 2) ≤ ∑ j, M i j * y * (κ₀ - κ / 2 * (c j / (A * y + B)) ^ 2)) :
    MonotoneOn (fun y : ℝ =>
      ∑ i, (κ₀ - κ / 2 * (c i / (A * y + B)) ^ 2) +
        y / γ * ∑ i, (κ₀ - κ / 2 * (c i / (A * y + B)) ^ 2) *
          ∑ j, M i j * (κ₀ - κ / 2 * (c j / (A * y + B)) ^ 2)) (Set.Ioi 0) := by
  set T : Fin n → ℝ → ℝ := fun i y => κ₀ - κ / 2 * (c i / (A * y + B)) ^ 2 with hT
  set Tp : Fin n → ℝ → ℝ := fun i y => κ * A * c i ^ 2 / (A * y + B) ^ 3 with hTp
  have hT' : ∀ i, ∀ y : ℝ, 0 < y → HasDerivAt (T i) (Tp i y) y := by
    intro i y hy
    have hDy := (hD y hy).ne'
    have hd : HasDerivAt (fun y : ℝ => A * y + B) A y := by
      have := ((hasDerivAt_id' y).const_mul A).add_const B
      simpa using this
    have hq : HasDerivAt (fun y : ℝ => c i / (A * y + B)) (-(c i * A) / (A * y + B) ^ 2) y :=
      ((hasDerivAt_const y (c i)).div hd hDy).congr_deriv (by ring)
    have h := (hasDerivAt_const y κ₀).sub ((hq.pow 2).const_mul (κ / 2))
    exact h.congr_deriv (by
      show _ = κ * A * c i ^ 2 / (A * y + B) ^ 3
      generalize A * y + B = D at hDy ⊢
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
      field_simp
      ring)
  have hTp0 : ∀ i y, 0 < y → 0 ≤ Tp i y := by
    intro i y hy
    have := hD y hy
    simp only [hTp]
    positivity
  let Gf : ℝ → ℝ := fun y => ∑ i, T i y + y / γ * ∑ i, T i y * ∑ j, M i j * T j y
  let Q : ℝ → ℝ := fun y => ∑ i, T i y * ∑ j, M i j * T j y
  let G' : ℝ → ℝ := fun y => ∑ i, Tp i y + (1 / γ * Q y +
    y / γ * ∑ i, (Tp i y * ∑ j, M i j * T j y + T i y * ∑ j, M i j * Tp j y))
  have hG : ∀ y : ℝ, 0 < y → HasDerivAt Gf (G' y) y := by
    intro y hy
    have h1 : HasDerivAt (fun y => ∑ i, T i y) (∑ i, Tp i y) y :=
      HasDerivAt.fun_sum (fun i _ => hT' i y hy)
    have h2 : ∀ i, HasDerivAt (fun y => ∑ j, M i j * T j y) (∑ j, M i j * Tp j y) y := fun i =>
      HasDerivAt.fun_sum (fun j _ => (hT' j y hy).const_mul (M i j))
    have h3 : HasDerivAt (fun y => ∑ i, T i y * ∑ j, M i j * T j y)
        (∑ i, (Tp i y * ∑ j, M i j * T j y + T i y * ∑ j, M i j * Tp j y)) y :=
      HasDerivAt.fun_sum (fun i _ => (hT' i y hy).mul (h2 i))
    have h4 : HasDerivAt (fun y : ℝ => y / γ) (1 / γ) y := (hasDerivAt_id' y).div_const γ
    exact h1.add (h4.mul h3)
  have hnonneg : ∀ y : ℝ, 0 < y → 0 ≤ G' y := by
    intro y hy
    have hsym : ∑ i, T i y * ∑ j, M i j * Tp j y = ∑ i, Tp i y * ∑ j, M i j * T j y := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hMsym j i]
      ring
    have hsplit : ∑ i, (Tp i y * ∑ j, M i j * T j y + T i y * ∑ j, M i j * Tp j y) =
        2 * ∑ i, Tp i y * ∑ j, M i j * T j y := by
      rw [Finset.sum_add_distrib, hsym]; ring
    have hexp : G' y = ∑ i, Tp i y * (1 + 2 * (y / γ) * ∑ j, M i j * T j y) + 1 / γ * Q y := by
      simp only [G', hsplit]
      have : ∑ i, Tp i y * (1 + 2 * (y / γ) * ∑ j, M i j * T j y) =
          ∑ i, Tp i y + 2 * (y / γ) * ∑ i, Tp i y * ∑ j, M i j * T j y := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [this]; ring
    rw [hexp]
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (hTp0 i y hy)
      have h := h24 i y hy
      have e : ∑ j, M i j * y * T j y = y * ∑ j, M i j * T j y := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      have h' : -(γ / 2) ≤ y * ∑ j, M i j * T j y := by rw [← e]; exact h
      have : 2 * (y / γ) * ∑ j, M i j * T j y = 2 / γ * (y * ∑ j, M i j * T j y) := by
        field_simp
      rw [this]
      have h2 : 2 / γ * (-(γ / 2)) = -1 := by field_simp
      have h3 := mul_le_mul_of_nonneg_left h' (by positivity : (0:ℝ) ≤ 2 / γ)
      linarith
    · exact mul_nonneg (by positivity) (hMpsd (fun i => T i y))
  have hderiv : ∀ y ∈ interior (Set.Ioi (0:ℝ)), deriv Gf y = G' y := by
    intro y hy
    rw [interior_Ioi] at hy
    exact (hG y hy).deriv
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro y hy
    exact (hG y hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    exact (hG y hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [hderiv y hy]
    rw [interior_Ioi] at hy
    exact hnonneg y hy

lemma clu2_gs_mono_full {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr : ℝ) (hα0 : 0 < α) (hγr : 0 < γr)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc)
    (c : Fin n → ℝ)
    (h24 : Cond24 S γr ρ T t α κ κc κ₀ c) :
    MonotoneOn (gStar S γr ρ T t α κ κc κ₀ c) (Set.Ioi 0) := by
  obtain ⟨hb, hbc, hsum⟩ := clu2_beta_facts ρ T t hρ hT ht
  have hMherm : (S⁻¹).IsHermitian := hS.inv.isHermitian
  have hMsym : ∀ i j, S⁻¹ i j = S⁻¹ j i := by
    intro i j
    have := hMherm.apply i j
    simpa using this.symm
  have hMpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, v i * ∑ j, S⁻¹ i j * v j := fun v =>
    clu2_q_nonneg S hS v
  have hmono := clu2_mono_core (S⁻¹) hMsym hMpsd γr κ κ₀
    (α * ClimateImpact.Interaction.beta ρ T t * κ) (ClimateImpact.Interaction.betaC ρ T t * κc)
    hγr hκ (mul_nonneg (mul_nonneg hα0.le hb) hκ.le) c
    (fun y hy => clu2_D_pos α ρ T t κ κc y hα0 hρ hT ht hκ hκc hy)
    (fun i y hy => h24 i y hy)
  exact hmono

theorem solution {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h24 : Cond24 S γr ρ T t α κ κc κ₀ c) :
    MonotoneOn (gStar S γr ρ T t α κ κc κ₀ c) (Set.Ioi 0) :=
  clu2_gs_mono_full S hS α γr hα0 hγr ρ T t hρ hT ht κ κc κ₀ hκ hκc c h24
