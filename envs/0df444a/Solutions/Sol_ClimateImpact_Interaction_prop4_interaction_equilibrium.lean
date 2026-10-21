-- Prove2me | solution 1 for ClimateImpact.Interaction.prop4_interaction_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T05:43:53.741987+00:00
-- url     : https://prove2.me/submissions/a817b718-c407-4dbe-8797-0dcc603e9f16

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Interaction_Game

set_option autoImplicit false

namespace P47646471

open ClimateImpact.Interaction

lemma quad_max {a g : ℝ} (ha : 0 < a) : (∀ u : ℝ, g * u - a * u ^ 2 ≤ 0) ↔ g = 0 := by
  constructor
  · intro h
    by_contra hg
    have h0 := h (g / (2 * a))
    have h1 : g * (g / (2 * a)) - a * (g / (2 * a)) ^ 2 = g ^ 2 / (4 * a) := by
      field_simp; ring
    rw [h1] at h0
    have hg2 : 0 < g ^ 2 := lt_of_le_of_ne (sq_nonneg g) (Ne.symm (pow_ne_zero 2 hg))
    have : 0 < g ^ 2 / (4 * a) := div_pos hg2 (by linarith)
    linarith
  · rintro rfl u
    nlinarith [sq_nonneg u]

lemma sum_update {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (z : ℝ) :
    ∑ j, Function.update x i z j = ∑ j, x j - x i + z := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_sdiff (s₁ := {i}) (s₂ := Finset.univ) (f := x) (Finset.subset_univ _)
  rw [Finset.sum_singleton] at h
  linarith

lemma payoff_update {n : ℕ} (ρ T α : ℝ) (κ κc κ₀ κc₀ : ℝ → ℝ) (c : Fin n → ℝ → ℝ)
    (ε t : ℝ) (i : Fin n) (x : Fin n → ℝ) (z : ℝ) :
    stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i (Function.update x i z)
      = (betaC ρ T t * κc₀ t + α * beta ρ T t * κ₀ t)
        - (betaC ρ T t * κc t + α * beta ρ T t * κ t) / 2
          * (z ^ 2 + ε * z * ((∑ j, x j - x i + z) / n)) + c i t * z := by
  unfold stagePayoff interExt avg
  rw [sum_update, Function.update_self]
  ring

lemma K_pos (ρ T α : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (hα0 : 0 < α) (κ κc : ℝ → ℝ) (t : ℝ)
    (ht : t ∈ Set.Icc 0 T) (hκ : 0 < κ t) (hκc : 0 < κc t) :
    0 < betaC ρ T t * κc t + α * beta ρ T t * κ t := by
  have hρT : 0 < ρ * T := mul_pos hρ hT
  have hd : 0 < 1 - Real.exp (-(ρ * T)) := by
    have : Real.exp (-(ρ * T)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this; linarith
  have h1 : 0 ≤ betaC ρ T t := by
    unfold betaC
    exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [ht.2]))) hd.le
  have h2 : 0 ≤ beta ρ T t := by
    unfold beta
    have e0 : Real.exp (-(ρ * t)) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [ht.1])
    exact div_nonneg (sub_nonneg.mpr e0) hd.le
  have h3 : betaC ρ T t + beta ρ T t = 1 := by
    unfold betaC beta
    rw [← add_div, div_eq_one_iff_eq hd.ne']
    ring
  set m := min (κc t) (α * κ t) with hmdef
  have hm : 0 < m := lt_min hκc (mul_pos hα0 hκ)
  have hm1 : m ≤ κc t := min_le_left _ _
  have hm2 : m ≤ α * κ t := min_le_right _ _
  have e1 : 0 ≤ betaC ρ T t * (κc t - m) := mul_nonneg h1 (by linarith)
  have e2 : 0 ≤ beta ρ T t * (α * κ t - m) := mul_nonneg h2 (by linarith)
  have e3 : betaC ρ T t * κc t + α * beta ρ T t * κ t
      = betaC ρ T t * (κc t - m) + beta ρ T t * (α * κ t - m)
        + m * (betaC ρ T t + beta ρ T t) := by ring
  rw [e3, h3]
  linarith

lemma nash_iff {n : ℕ} (hn : 0 < n) (ρ T α : ℝ) (κ κc κ₀ κc₀ : ℝ → ℝ) (c : Fin n → ℝ → ℝ)
    (ε t : ℝ) (hε : 0 ≤ ε) (hK : 0 < betaC ρ T t * κc t + α * beta ρ T t * κ t)
    (x : Fin n → ℝ) :
    IsStageNash ρ T α κ κc κ₀ κc₀ c ε t x ↔
      ∀ i, x i * (2 * n + ε) + ε * (∑ j, x j)
        = 2 * n * (c i t / (betaC ρ T t * κc t + α * beta ρ T t * κ t)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  unfold IsStageNash
  apply forall_congr'
  intro i
  set K := betaC ρ T t * κc t + α * beta ρ T t * κ t with hKdef
  set D := ∑ j, x j with hD
  have hx : stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i x
      = stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i (Function.update x i (x i)) := by
    rw [Function.update_eq_self]
  rw [hx]
  set a := K / 2 * (1 + ε / n) with ha
  set g := c i t - K / 2 * (2 * (1 + ε / n) * x i + ε * (D - x i) / n) with hg
  have hapos : 0 < a := by
    have : 0 < 1 + ε / n := by have := div_nonneg hε hnR.le; linarith
    exact mul_pos (by linarith) this
  have e : ∀ u : ℝ, stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i (Function.update x i (x i + u))
      - stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i (Function.update x i (x i))
      = g * u - a * u ^ 2 := by
    intro u
    rw [payoff_update, payoff_update]
    ring
  have hiff : (∀ z : ℝ, stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i (Function.update x i z)
      ≤ stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i (Function.update x i (x i)))
      ↔ ∀ u : ℝ, g * u - a * u ^ 2 ≤ 0 := by
    constructor
    · intro h u
      linarith [h (x i + u), e u]
    · intro h z
      have h1 := h (z - x i)
      have h2 := e (z - x i)
      have hz : x i + (z - x i) = z := by ring
      rw [hz] at h2
      linarith
  rw [hiff, quad_max hapos]
  have hgf : g = K / (2 * n) * (2 * n * (c i t / K) - (x i * (2 * n + ε) + ε * D)) := by
    rw [hg]
    field_simp
    ring
  rw [hgf, mul_eq_zero, sub_eq_zero]
  have hne : K / (2 * n) ≠ 0 := by positivity
  constructor
  · rintro (h | h)
    · exact absurd h hne
    · exact h.symm
  · intro h; right; exact h.symm

end P47646471

open ClimateImpact.Interaction in
theorem solution (n : ℕ) (hn : 0 < n) (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (κ κc κ₀ κc₀ : ℝ → ℝ) (hκ : ∀ t ∈ Set.Icc 0 T, 0 < κ t)
    (hκc : ∀ t ∈ Set.Icc 0 T, 0 < κc t)
    (c : Fin n → ℝ → ℝ) (hc : ∀ i, ∀ t ∈ Set.Icc 0 T, 0 ≤ c i t)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ t ∈ Set.Icc 0 T,
      (∀ x : Fin n → ℝ, IsStageNash ρ T α κ κc κ₀ κc₀ c ε t x ↔
          x = interactionRate ρ T α κ κc c ε t) ∧
        ∀ i, interactionRate ρ T α κ κc c ε t i ≤ noInt ρ T α κ κc c t i := by
  intro t ht
  have hK := P47646471.K_pos ρ T α hρ hT hα0 κ κc t ht (hκ t ht) (hκc t ht)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  set K := betaC ρ T t * κc t + α * beta ρ T t * κ t with hKdef
  set ψ := noInt ρ T α κ κc c t with hψdef
  have hψ : ∀ i, c i t / K = ψ i := fun i => rfl
  set P := ∑ j, ψ j with hP
  have hden : 0 < 2 * (n:ℝ) + (n + 1) * ε := by
    have : 0 ≤ ((n:ℝ) + 1) * ε := mul_nonneg (by positivity) hε
    linarith
  have hden2 : 0 < 2 * (n:ℝ) + ε := by linarith
  set D0 := 2 * n * P / (2 * n + (n + 1) * ε) with hD0
  have hr : ∀ i, interactionRate ρ T α κ κc c ε t i = (2 * n * ψ i - ε * D0) / (2 * n + ε) := by
    intro i
    simp only [interactionRate, avg, hD0]
    rw [← hψdef, ← hP]
    field_simp
    ring
  have hsumr : ∑ j, interactionRate ρ T α κ κc c ε t j = D0 := by
    simp only [hr]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hP, hD0]
    field_simp
    ring
  refine ⟨fun x => ?_, fun i => ?_⟩
  · rw [P47646471.nash_iff hn ρ T α κ κc κ₀ κc₀ c ε t hε hK x]
    simp only [← hKdef, hψ]
    constructor
    · intro h
      have hsum : ∑ i, (x i * (2 * n + ε) + ε * ∑ j, x j) = ∑ i, 2 * (n:ℝ) * ψ i :=
        Finset.sum_congr rfl (fun i _ => h i)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← hP] at hsum
      have hDx : ∑ j, x j = D0 := by
        rw [hD0, eq_div_iff hden.ne']
        linarith
      funext i
      rw [hr, eq_div_iff hden2.ne']
      have := h i
      rw [hDx] at this
      linarith
    · rintro rfl i
      rw [hsumr, hr]
      field_simp
      ring
  · have hψ0 : ∀ j, 0 ≤ ψ j := fun j => by
      rw [← hψ]; exact div_nonneg (hc j t ht) hK.le
    have havg : 0 ≤ avg ψ := by
      unfold avg; exact div_nonneg (Finset.sum_nonneg (fun j _ => hψ0 j)) hnR.le
    have hterm : 0 ≤ ε / (2 * n + ε) * (ψ i + 2 * n ^ 2 / (2 * n + (n + 1) * ε) * avg ψ) :=
      mul_nonneg (div_nonneg hε hden2.le)
        (add_nonneg (hψ0 i) (mul_nonneg (div_nonneg (by positivity) hden.le) havg))
    show interactionRate ρ T α κ κc c ε t i ≤ ψ i
    simp only [interactionRate]
    rw [← hψdef]
    linarith
