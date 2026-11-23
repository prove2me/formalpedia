-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.reduced_phase_critical_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:43.400175+00:00
-- url     : https://prove2.me/submissions/525200a5-8d5e-4b6a-9ac1-1ba38b0f4863

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wM_zero_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_poly_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_poly_deriv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_poly_deriv_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_superSum_wM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.CornerEntryCritical := by
  intro m z D σ ρ' X B hz hD hX hx
  have hD' : D = -((-z) ^ m * z * z) := by
    have h1 : ((-1 : ℂ) ^ (m + 3)) * ((-1 : ℂ) ^ (m + 3)) = 1 := by
      rw [← mul_pow]; simp
    calc D = ((-1 : ℂ) ^ (m + 3)) * ((-1 : ℂ) ^ (m + 3) * D) := by rw [← mul_assoc, h1, one_mul]
      _ = ((-1 : ℂ) ^ (m + 3)) * z ^ (m + 2) := by rw [hD]
      _ = -((-z) ^ m * z * z) := by rw [neg_pow z m]; ring
  have hCne : (-z) ^ m * z ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hz)) hz
  obtain ⟨k0, k1, -⟩ := key m z X B hX hx m
  have hC0 : Cof X B 0 = (-z) ^ m * z := by
    unfold Cof
    rw [poly_zero m (fun j => ((-X) ^ j *ᵥ B) 0)]
    exact k1 0 (by simp)
  have hR0 : R0 X B ρ' 0 = 0 := by
    unfold R0
    rw [poly_zero m (fun j => ∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [k0 k.succ (by simp), mul_zero]
  have hval : rho1 D σ ρ' X B 0 = z := by
    unfold rho1
    rw [hC0, hR0, hD', zero_pow (by omega)]
    simp only [zero_mul, zero_sub, neg_neg, sub_zero]
    exact mul_div_cancel_left₀ z hCne
  refine ⟨hval, ?_⟩
  have hnum0 : (0 : ℂ) ^ (m + 1) * σ - D - R0 X B ρ' 0 = (-z) ^ m * z * z := by
    rw [hR0, hD', zero_pow (by omega)]; ring
  have hCne' : Cof X B 0 ≠ 0 := by rw [hC0]; exact hCne
  cases m with
  | zero =>
    have hNum : HasDerivAt (fun t : ℂ => t ^ (0 + 1) * σ - D - R0 X B ρ' t) (1 * σ - 0) 0 := by
      have h1 : HasDerivAt (fun t : ℂ => t ^ (0 + 1) * σ - D) (1 * σ) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const σ).sub_const D
      exact h1.sub (poly_deriv_zero (fun j => ∑ k : Fin 0, ρ' k * ((-X) ^ j *ᵥ B) k.succ))
    have hCof : HasDerivAt (fun t : ℂ => Cof X B t) 0 0 :=
      poly_deriv_zero (fun j => ((-X) ^ j *ᵥ B) 0)
    have hdiv := hNum.div hCof hCne'
    refine hdiv.congr_deriv ?_
    have hs : superSum (wMat (0 + 2) * Mcoord 0 X B (Fin.cons z ρ') σ) = σ := by
      unfold superSum
      rw [Fin.sum_univ_succ]
      simpa using wM_zero_last X B (Fin.cons z ρ') σ
    rw [hs, hC0]
    field_simp
    simp
  | succ m =>
    obtain ⟨l0, l1, l2⟩ := key (m + 1) z X B hX hx m
    have hNum : HasDerivAt (fun t : ℂ => t ^ (m + 1 + 1) * σ - D - R0 X B ρ' t)
        (0 - ρ' 0 * ((-z) ^ m * z)) 0 := by
      have h1 : HasDerivAt (fun t : ℂ => t ^ (m + 1 + 1) * σ - D) 0 0 := by
        simpa using ((hasDerivAt_pow (m + 1 + 1) (0 : ℂ)).mul_const σ).sub_const D
      have h2 := poly_deriv_succ m (fun j => ∑ k : Fin (m + 1), ρ' k * ((-X) ^ j *ᵥ B) k.succ)
      have h3 : ∑ k : Fin (m + 1), ρ' k * ((-X) ^ m *ᵥ B) k.succ = ρ' 0 * ((-z) ^ m * z) := by
        rw [Fin.sum_univ_succ, l1 (Fin.succ 0) (by simp; omega)]
        rw [Finset.sum_eq_zero, add_zero]
        intro k _
        rw [l0 k.succ.succ (by simp; omega), mul_zero]
      rw [h3] at h2
      exact h1.sub h2
    have hCof : HasDerivAt (fun t : ℂ => Cof X B t)
        ((-z) ^ m * ∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2)) 0 := by
      have h2 := poly_deriv_succ m (fun j => ((-X) ^ j *ᵥ B) 0)
      rw [l2 0 (by simp)] at h2
      exact h2
    have hdiv := hNum.div hCof hCne'
    refine hdiv.congr_deriv ?_
    have hc1 : (Fin.cons z ρ' : Fin (m + 2) → ℂ) 1 = ρ' 0 := Fin.cons_succ (α := fun _ => ℂ) z ρ' 0
    rw [superSum_wM, hc1, hnum0, hC0]
    have ha : (-z) ^ m ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hz)
    rw [pow_succ]
    generalize (-z) ^ m = a at ha
    generalize ∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2) = T
    field_simp
    ring
end Formalism.FourierDecayAlt.P
