-- Prove2me | solution 1 for CalibratedCE.Convergence.empDist_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:47:51.043986+00:00
-- url     : https://prove2.me/submissions/7109f0f0-8797-4ef2-abcf-2496c09248b9

import Mathlib
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_EmpDist

namespace CalibratedCE.Convergence

theorem aux_edd_part1 {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (f₁ : ℕ → Fin n → ℝ)
    (y : ℕ → Fin n) (t : ℕ) (a : Fin m) (b : Fin n) :
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (((Finset.range t).filter (fun r => f₁ r = p ∧ y r = b)).card : ℝ) := by
  unfold empDist
  rw [div_eq_inv_mul]
  congr 1
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := f₁)
    (t := ((Finset.range t).image f₁).filter (fun p => R₁ p = a))]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, h4 ▸ hp.2, h3⟩, h4⟩
  · intro r hr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    exact ⟨⟨r, hr.1, rfl⟩, hr.2.1⟩

theorem aux_edd_rhoN {n : ℕ} (f₁ : ℕ → Fin n → ℝ) (y : ℕ → Fin n) (t : ℕ) (b : Fin n)
    (p : Fin n → ℝ) (hp : p ∈ (Finset.range t).image f₁) :
    Shared.rho f₁ y p b t * (Shared.N f₁ p t : ℝ) =
      (((Finset.range t).filter (fun r => f₁ r = p ∧ y r = b)).card : ℝ) := by
  have hN : Shared.N f₁ p t ≠ 0 := by
    unfold Shared.N
    rw [Finset.mem_image] at hp
    obtain ⟨s, hs, hsp⟩ := hp
    apply Finset.card_ne_zero.mpr
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, hsp⟩⟩
  unfold Shared.rho
  rw [if_neg hN]
  have : (Shared.N f₁ p t : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp

end CalibratedCE.Convergence

open CalibratedCE CalibratedCE.Convergence

theorem solution {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (f₁ : ℕ → Fin n → ℝ)
    (y : ℕ → Fin n) (t : ℕ) (a : Fin m) (b : Fin n) :
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (((Finset.range t).filter (fun r => f₁ r = p ∧ y r = b)).card : ℝ) ∧
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          Shared.rho f₁ y p b t * (Shared.N f₁ p t : ℝ) ∧
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          p b * (Shared.N f₁ p t : ℝ) +
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ) := by
  have h1 := aux_edd_part1 R₁ f₁ y t a b
  have h2 : empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          Shared.rho f₁ y p b t * (Shared.N f₁ p t : ℝ) := by
    rw [h1]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    exact (aux_edd_rhoN f₁ y t b p hp.1).symm
  refine ⟨h1, h2, ?_⟩
  rw [h2, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring
