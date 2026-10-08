-- Prove2me | solution 1 for CVPricing.Regret.design_matrix_eigenvalue_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:31:24.491232+00:00
-- url     : https://prove2.me/submissions/c4ddd299-f874-45d7-be78-add55a0b1aa1

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares

set_option autoImplicit false

open Matrix KeskinZeevi.SufficientConditions in
theorem CVPricing_Regret_dmeb_fisher_quad (p : ℕ → ℝ) (t : ℕ) (y : Fin 2 → ℝ) :
    y ⬝ᵥ (fisherOf p t *ᵥ y) = ∑ s ∈ Finset.Icc 1 t, (y 0 + p s * y 1) ^ 2 := by
  have h00 : fisherOf p t 0 0 = ∑ s ∈ Finset.Icc 1 t, (1 : ℝ) := by
    simp [fisherOf, Matrix.sum_apply]
  have h01 : fisherOf p t 0 1 = ∑ s ∈ Finset.Icc 1 t, p s := by
    simp [fisherOf, Matrix.sum_apply]
  have h10 : fisherOf p t 1 0 = ∑ s ∈ Finset.Icc 1 t, p s := by
    simp [fisherOf, Matrix.sum_apply]
  have h11 : fisherOf p t 1 1 = ∑ s ∈ Finset.Icc 1 t, p s ^ 2 := by
    simp [fisherOf, Matrix.sum_apply]
  simp only [dotProduct, mulVec, Fin.sum_univ_two, h00, h01, h10, h11]
  have : ∀ s, (y 0 + p s * y 1) ^ 2 = y 0 * y 0 * 1 + y 0 * y 1 * p s + y 1 * y 0 * p s
      + y 1 * y 1 * p s ^ 2 := fun s => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

open Matrix KeskinZeevi.SufficientConditions in
theorem CVPricing_Regret_dmeb_info (p : ℕ → ℝ) (t : ℕ) (ht : 0 < t) :
    (t : ℝ) * infoMetricOf p t
      = (t : ℝ) * ∑ s ∈ Finset.Icc 1 t, p s ^ 2 - (∑ s ∈ Finset.Icc 1 t, p s) ^ 2 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hcard : ∑ s ∈ Finset.Icc 1 t, (1 : ℝ) = t := by simp
  unfold infoMetricOf avgPriceOf
  set b := ∑ s ∈ Finset.Icc 1 t, p s
  have : ∀ s, (p s - b / t) ^ 2 = p s ^ 2 - 2 * (b / t) * p s + (b / t) ^ 2 * 1 :=
    fun s => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcard]
  field_simp
  ring

open Matrix KeskinZeevi.SufficientConditions in
theorem solution (pl ph : ℝ) (hpl : 0 < pl) (hlh : pl < ph)
    (p : ℕ → ℝ) (t : ℕ) (ht : 2 ≤ t) (hp : ∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc pl ph)
    (h12 : p 1 ≠ p 2) :
    (⨆ y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1}, y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1))
        ≤ (1 + ph ^ 2) * t ∧
      infoMetricOf p t ≤ (1 + ph ^ 2) * minRayleigh (fisherOf p t) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hcard : ∑ s ∈ Finset.Icc 1 t, (1 : ℝ) = t := by simp
  have hne : Nonempty {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1} :=
    ⟨⟨![1, 0], by simp⟩⟩
  have hsq : ∀ s ∈ Finset.Icc 1 t, p s ^ 2 ≤ ph ^ 2 := by
    intro s hs
    obtain ⟨h1, h2⟩ := hp s hs
    nlinarith
  have hc : ∑ s ∈ Finset.Icc 1 t, p s ^ 2 ≤ t * ph ^ 2 := by
    calc ∑ s ∈ Finset.Icc 1 t, p s ^ 2 ≤ ∑ s ∈ Finset.Icc 1 t, ph ^ 2 := Finset.sum_le_sum hsq
      _ = t * ph ^ 2 := by simp
  -- upper bound for each unit vector
  have hup : ∀ y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1},
      y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1) ≤ (1 + ph ^ 2) * t := by
    intro y
    obtain ⟨y, hy⟩ := y
    rw [CVPricing_Regret_dmeb_fisher_quad]
    calc ∑ s ∈ Finset.Icc 1 t, (y 0 + p s * y 1) ^ 2
        ≤ ∑ s ∈ Finset.Icc 1 t, (1 + ph ^ 2) := by
          apply Finset.sum_le_sum
          intro s hs
          have h := hsq s hs
          have h' : (y 0 + p s * y 1) ^ 2 ≤ (1 + p s ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by
            nlinarith [sq_nonneg (p s * y 0 - y 1)]
          rw [hy] at h'
          linarith
      _ = (1 + ph ^ 2) * t := by simp; ring
  refine ⟨ciSup_le hup, ?_⟩
  -- lower bound
  have hlow : ∀ y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1},
      infoMetricOf p t / (1 + ph ^ 2) ≤ y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1) := by
    intro y
    obtain ⟨y, hy⟩ := y
    have hQ := CVPricing_Regret_dmeb_fisher_quad p t y
    have hinfo := CVPricing_Regret_dmeb_info p t (by omega)
    simp only at hQ ⊢
    set Q := y ⬝ᵥ (fisherOf p t *ᵥ y)
    set b := ∑ s ∈ Finset.Icc 1 t, p s
    set c := ∑ s ∈ Finset.Icc 1 t, p s ^ 2
    have hQnn : 0 ≤ Q := by
      rw [hQ]; exact Finset.sum_nonneg (fun s _ => sq_nonneg _)
    have hQexp : Q = t * y 0 ^ 2 + 2 * b * y 0 * y 1 + c * y 1 ^ 2 := by
      rw [hQ]
      have : ∀ s, (y 0 + p s * y 1) ^ 2 = y 0 ^ 2 * 1 + (2 * y 0 * y 1) * p s
          + y 1 ^ 2 * p s ^ 2 := fun s => by ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hcard]
      ring
    have hkey : Q * (t + c) - (t * c - b ^ 2) * (y 0 ^ 2 + y 1 ^ 2)
        = (t * y 0 + b * y 1) ^ 2 + (b * y 0 + c * y 1) ^ 2 := by
      rw [hQexp]; ring
    rw [hy, mul_one] at hkey
    have h1 : (t : ℝ) * infoMetricOf p t ≤ Q * (t + c) := by
      nlinarith [sq_nonneg (t * y 0 + b * y 1), sq_nonneg (b * y 0 + c * y 1)]
    have h2 : Q * (t + c) ≤ Q * (t * (1 + ph ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hQnn
      nlinarith
    have h3 : infoMetricOf p t ≤ Q * (1 + ph ^ 2) := by
      have : (t : ℝ) * infoMetricOf p t ≤ t * (Q * (1 + ph ^ 2)) := by nlinarith
      exact le_of_mul_le_mul_left this htR
    rw [div_le_iff₀ (by positivity)]
    exact h3
  have := le_ciInf hlow
  unfold minRayleigh
  rw [div_le_iff₀ (by positivity)] at this
  linarith
