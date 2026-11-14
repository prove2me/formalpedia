-- Prove2me | solution 1 for BosonicLearn.gaussianState_exists_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T21:05:12.721025+00:00
-- url     : https://prove2.me/submissions/c73abc6f-a187-48a0-bbe5-2d29a7ad9a82

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState
import Theorems.Thm_BosonicLearn_state_gaussian_mixture
import Theorems.Thm_BosonicLearn_gaussianAt_of_characteristic

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

/-- Grouped index of an interleaved quadrature index. -/
private def idx {n : ℕ} (a : Fin n × Fin 2) : Fin n ⊕ Fin n :=
  if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1

theorem solution {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (h : IsGaussianState ρ μ S)
    (μ' : Fin n ⊕ Fin n → ℝ) (S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS' : (S' - S).PosSemidef) :
    ∃ ρ' : State (Occupation (Fin n)), IsGaussianState ρ' μ' S' := by
  have hG : GaussianAt ρ.coefficients (fun a => μ (idx a)) (fun a b => 2 * S (idx a) (idx b)) := h
  have hT : ((S' - S).submatrix (idx (n := n)) idx).PosSemidef := hS'.submatrix idx
  obtain ⟨ρ', hχ⟩ := state_gaussian_mixture ρ (fun a => μ' (idx a) - μ (idx a))
    ((S' - S).submatrix (idx (n := n)) idx) hT
  refine ⟨ρ', ?_⟩
  show GaussianAt ρ'.coefficients (fun a => μ' (idx a)) (fun a b => 2 * S' (idx a) (idx b))
  -- symmetry of the two covariance forms
  have hSsym : ∀ a b : Fin n × Fin 2, S (idx b) (idx a) = S (idx a) (idx b) := by
    intro a b
    have h1 := congrFun (congrFun hG.1.2.1 a) b
    have h2 : (2 : ℝ) * S (idx b) (idx a) = 2 * S (idx a) (idx b) := h1
    linarith
  have hDsym : ∀ x y : Fin n ⊕ Fin n, (S' - S) y x = (S' - S) x y := by
    intro x y
    have h1 := congrFun (congrFun hS'.isHermitian.eq x) y
    simpa [Matrix.conjTranspose_apply] using h1
  have hS'sym : ∀ a b : Fin n × Fin 2, S' (idx b) (idx a) = S' (idx a) (idx b) := by
    intro a b
    have h1 := hDsym (idx a) (idx b)
    simp only [Matrix.sub_apply] at h1
    linarith [hSsym a b]
  apply gaussianAt_of_characteristic
  · apply Matrix.ext
    intro a b
    show 2 * S' (idx b) (idx a) = 2 * S' (idx a) (idx b)
    rw [hS'sym a b]
  · intro ξ
    rw [hχ ξ, hG.2 ξ, ← Complex.exp_add]
    congr 1
    have hm : meanForm (fun a : Fin n × Fin 2 => μ' (idx a) - μ (idx a)) ξ +
        meanForm (fun a : Fin n × Fin 2 => μ (idx a)) ξ =
        meanForm (fun a : Fin n × Fin 2 => μ' (idx a)) ξ := by
      unfold meanForm
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hv : varianceForm ((S' - S).submatrix (idx (n := n)) idx) ξ / 2 +
        varianceForm (fun a b : Fin n × Fin 2 => 2 * S (idx a) (idx b)) ξ / 4 =
        varianceForm (fun a b : Fin n × Fin 2 => 2 * S' (idx a) (idx b)) ξ / 4 := by
      unfold varianceForm
      rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Matrix.submatrix_apply, Matrix.sub_apply]
      ring
    rw [← hm]
    have hv' : varianceForm (fun a b : Fin n × Fin 2 => 2 * S' (idx a) (idx b)) ξ =
        2 * varianceForm ((S' - S).submatrix (idx (n := n)) idx) ξ +
          varianceForm (fun a b : Fin n × Fin 2 => 2 * S (idx a) (idx b)) ξ := by linarith
    rw [hv']
    push_cast
    ring
