-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_A_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:32:28.684091+00:00
-- url     : https://prove2.me/submissions/82faefc3-995a-4b4e-a2fe-145c7eda179d

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

open BoundedEntropyGames.ConvRate

theorem BGE_A11_expect {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜]
    (pA : 𝒜 → ℝ) (w : 𝒳 → 𝒜 → ℝ) :
    ∑ f : 𝒳 → 𝒜, pF pA f * ∏ x, w x (f x) = ∏ x, ∑ b, pA b * w x b := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset 𝒜)), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold pF
  rw [← Finset.prod_mul_distrib]

theorem solution {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜] [DecidableEq 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) (g : 𝒳 → ℝ) (a : 𝒜) :
    ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)| ^ 2
        = pA a * (1 - pA a) * ∑ x, g x ^ 2 ∧
      ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)| ^ 2
        ≤ pA a * ∑ x, g x ^ 2 := by
  obtain ⟨hnn, hsum⟩ := hpA
  set c : 𝒜 → ℝ := fun b => (if b = a then 1 else 0) - pA a with hc
  have S0 : ∑ b, pA b = 1 := hsum
  have S1 : ∑ b, pA b * c b = 0 := by
    simp only [hc, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, S0, one_mul, sub_self]
  have S2 : ∑ b, pA b * (c b * c b) = pA a * (1 - pA a) := by
    have : ∀ b, pA b * (c b * c b) =
        (if b = a then pA a * (1 - 2 * pA a) else 0) + pA b * (pA a * pA a) := by
      intro b
      by_cases hb : b = a
      · subst hb; simp [hc]; try ring
      · simp [hc, hb]; try ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.sum_mul, S0]
    ring
  -- key pairwise expectation
  have pair : ∀ x x' : 𝒳, ∑ f : 𝒳 → 𝒜, pF pA f * (c (f x) * c (f x')) =
      if x = x' then pA a * (1 - pA a) else 0 := by
    intro x x'
    have h1 : ∀ f : 𝒳 → 𝒜, c (f x) * c (f x') =
        ∏ z, ((if z = x then c (f z) else 1) * (if z = x' then c (f z) else 1)) := by
      intro f
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
      simp
    simp_rw [h1]
    rw [BGE_A11_expect pA (fun z b => (if z = x then c b else 1) * (if z = x' then c b else 1))]
    by_cases hxx : x = x'
    · subst hxx
      rw [if_pos rfl]
      have : ∀ z, ∑ b, pA b * ((if z = x then c b else 1) * (if z = x then c b else 1)) =
          if z = x then pA a * (1 - pA a) else 1 := by
        intro z
        by_cases hz : z = x
        · simp [hz, S2]
        · simp [hz, S0]
      simp_rw [this]
      rw [Finset.prod_ite_eq']
      simp
    · rw [if_neg hxx]
      apply Finset.prod_eq_zero (Finset.mem_univ x)
      simp [hxx, S1]
  have main : ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)| ^ 2
      = pA a * (1 - pA a) * ∑ x, g x ^ 2 := by
    have e : ∀ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)| ^ 2
        = ∑ x, ∑ x', g x * g x' * (pF pA f * (c (f x) * c (f x'))) := by
      intro f
      rw [sq_abs, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x' _ => ?_
      simp only [hc]; ring
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (𝒳 → 𝒜))) (t := (Finset.univ : Finset 𝒳)),
      ← Finset.mul_sum, pair]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  refine ⟨main, ?_⟩
  rw [main]
  have hpa := hnn a
  have hsq : 0 ≤ ∑ x, g x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have : pA a * (1 - pA a) ≤ pA a := by nlinarith
  exact mul_le_mul_of_nonneg_right this hsq
