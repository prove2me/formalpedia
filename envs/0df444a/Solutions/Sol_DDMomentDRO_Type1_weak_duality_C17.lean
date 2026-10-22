-- Prove2me | solution 1 for DDMomentDRO.Type1.weak_duality_C17
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:36:26.030147+00:00
-- url     : https://prove2.me/submissions/bbf1cb40-8abf-412d-9a11-fe4ce6119c11

import Mathlib
import Definitions.Def_DDMomentDRO_Type1_Setting

set_option autoImplicit false
open Matrix DDMomentDRO.Type1

theorem solution {I J K m : ℕ}
    (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (hbin : ∀ p ∈ S, ∀ i, p.1 i = 0 ∨ p.1 i = 1)
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ) (e : Fin m → Fin J → ℕ)
    (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ)
    (x : Fin I → ℝ) (p : Fin K → ℝ) (hp : p ∈ amb1 ξ e l u pl pu x)
    (α β : Fin m → ℝ) (γl γu : Fin K → ℝ) (hdual : DualFeas1 Qn ξ e x α β γl γu) :
    ∑ k, p k * Qn x k ≤ -(α ⬝ᵥ l x) + β ⬝ᵥ u x - γl ⬝ᵥ pl x + γu ⬝ᵥ pu x := by
  obtain ⟨hpl, hpu, hl, hu, hp0⟩ := hp
  obtain ⟨hα, hβ, hγl, hγu, hQ⟩ := hdual
  -- the moment vector m := ∑ p_k f(ξ_k)
  set mv : Fin m → ℝ := ∑ k, p k • momentFn e (ξ k) with hmv
  have step1 : ∑ k, p k * Qn x k ≤ ∑ k, p k * ((β - α) ⬝ᵥ momentFn e (ξ k) - γl k + γu k) := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (hQ k) (hp0 k)
  have step2 : ∑ k, p k * ((β - α) ⬝ᵥ momentFn e (ξ k) - γl k + γu k)
      = (β - α) ⬝ᵥ mv - γl ⬝ᵥ p + γu ⬝ᵥ p := by
    have a : ∑ k, p k * ((β - α) ⬝ᵥ momentFn e (ξ k)) = (β - α) ⬝ᵥ mv := by
      simp only [hmv, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    have b : ∑ k, p k * ((β - α) ⬝ᵥ momentFn e (ξ k) - γl k + γu k)
        = ∑ k, p k * ((β - α) ⬝ᵥ momentFn e (ξ k)) - ∑ k, γl k * p k + ∑ k, γu k * p k := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [b, a]
    rfl
  have e1 : (β - α) ⬝ᵥ mv = β ⬝ᵥ mv - α ⬝ᵥ mv := sub_dotProduct _ _ _
  have e2 : α ⬝ᵥ mv ≥ α ⬝ᵥ l x := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hl j) (hα j)
  have e3 : β ⬝ᵥ mv ≤ β ⬝ᵥ u x := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hu j) (hβ j)
  have e4 : γl ⬝ᵥ pl x ≤ γl ⬝ᵥ p := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (hpl k) (hγl k)
  have e5 : γu ⬝ᵥ p ≤ γu ⬝ᵥ pu x := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (hpu k) (hγu k)
  linarith

