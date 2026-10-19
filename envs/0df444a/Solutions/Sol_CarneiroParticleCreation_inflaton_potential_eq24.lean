-- Prove2me | solution 1 for CarneiroParticleCreation.inflaton_potential_eq24
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:39:58.874465+00:00
-- url     : https://prove2.me/submissions/339ae1ac-03df-43f8-ab75-4ee02c401eb7

import Mathlib

theorem solution (γ : ℝ) (hγ0 : 0 < γ) (hγ : γ < 4) (Hφ V : ℝ → ℝ)
    (hd : Differentiable ℝ Hφ) (hpos : ∀ φ, 0 < Hφ φ)
    (h21 : ∀ φ, 3 * Hφ φ ^ 2 = V φ + 2 * deriv Hφ φ ^ 2)
    (hV : ∀ φ, V φ = 3 * γ * Hφ φ ^ 2 / 4) :
    (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ φ, V φ =
        3 * γ * Hφ 0 ^ 2 / 4 * Real.exp (s * Real.sqrt (2 * (3 / 2 * ((4 - γ) / 2))) * φ)) ∧
    ∀ φ, deriv (deriv V) φ / V φ = 2 * (3 / 2 * ((4 - γ) / 2)) ∧
      (deriv V φ / V φ) ^ 2 = 2 * (3 / 2 * ((4 - γ) / 2)) := by
  set K := Real.sqrt (2 * (3 / 2 * ((4 - γ) / 2))) with hK
  have hK2 : K ^ 2 = 2 * (3 / 2 * ((4 - γ) / 2)) := Real.sq_sqrt (by nlinarith)
  have hKpos : 0 < K := Real.sqrt_pos.mpr (by nlinarith)
  set k := K / 2 with hk
  have hkpos : 0 < k := by positivity
  -- H'^2 = k^2 H^2
  have hsq : ∀ x, deriv Hφ x ^ 2 = (k * Hφ x) ^ 2 := by
    intro x
    have e := h21 x
    rw [hV] at e
    rw [mul_pow, hk, div_pow, hK2]
    nlinarith
  have hne : ∀ x ∈ (Set.univ : Set ℝ), deriv Hφ x ≠ 0 := by
    intro x _ h0
    have := hsq x
    rw [h0] at this
    have : 0 < (k * Hφ x) ^ 2 := by have := hpos x; positivity
    linarith
  -- constant sign (Darboux)
  obtain ⟨s, hs, hds⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ x, deriv Hφ x = s * k * Hφ x := by
    rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne convex_univ
      (fun x _ => (hd x).hasDerivAt.hasDerivWithinAt) hne with hneg | hpos'
    · refine ⟨-1, Or.inr rfl, fun x => ?_⟩
      have h1 := hneg x (Set.mem_univ _)
      have h2 := hsq x
      have h3 : 0 < k * Hφ x := mul_pos hkpos (hpos x)
      nlinarith
    · refine ⟨1, Or.inl rfl, fun x => ?_⟩
      have h1 := hpos' x (Set.mem_univ _)
      have h2 := hsq x
      have h3 : 0 < k * Hφ x := mul_pos hkpos (hpos x)
      nlinarith
  -- solve the ODE
  have hsol : ∀ x, Hφ x = Hφ 0 * Real.exp (s * k * x) := by
    have hg : ∀ x, HasDerivAt (fun y => Hφ y * Real.exp (-(s * k) * y)) 0 x := by
      intro x
      have h1 := (hd x).hasDerivAt.mul (((hasDerivAt_id x).const_mul (-(s * k))).exp)
      refine h1.congr_deriv ?_
      rw [hds x]; simp; ring
    intro x
    have := is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt) (fun y => (hg y).deriv) x 0
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    rw [← this, mul_assoc, ← Real.exp_add]
    simp
  set C := 3 * γ * Hφ 0 ^ 2 / 4 with hC
  have hCpos : 0 < C := by have := hpos 0; positivity
  have hVf : V = fun x => C * Real.exp (s * K * x) := by
    funext x
    rw [hV, hsol x, mul_pow, ← Real.exp_nat_mul]
    rw [hC, hk]; push_cast; ring_nf
  have hs2 : s ^ 2 = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  refine ⟨⟨s, hs, fun x => by rw [hVf]⟩, fun x => ?_⟩
  have hd1 : ∀ y, HasDerivAt V (C * (s * K) * Real.exp (s * K * y)) y := by
    intro y
    rw [hVf]
    have := (((hasDerivAt_id y).const_mul (s * K)).exp).const_mul C
    refine this.congr_deriv ?_; simp; ring
  have hd1' : deriv V = fun y => C * (s * K) * Real.exp (s * K * y) := funext fun y => (hd1 y).deriv
  have hd2 : HasDerivAt (deriv V) (C * (s * K) * ((s * K) * Real.exp (s * K * x))) x := by
    rw [hd1']
    have := (((hasDerivAt_id x).const_mul (s * K)).exp).const_mul (C * (s * K))
    refine this.congr_deriv ?_; simp only [id, mul_one]; ring
  have hE := Real.exp_pos (s * K * x)
  have hVx : V x = C * Real.exp (s * K * x) := by rw [hVf]
  rw [hd2.deriv, (hd1 x).deriv, hVx]
  constructor
  · field_simp; linear_combination (2 * K ^ 2) * hs2 + 2 * hK2
  · field_simp; linear_combination (2 * K ^ 2) * hs2 + 2 * hK2
