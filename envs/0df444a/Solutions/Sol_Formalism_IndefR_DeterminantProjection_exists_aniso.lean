-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.exists_aniso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:24.167859+00:00
-- url     : https://prove2.me/submissions/58950199-00eb-4af7-8679-360ece940341

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
import Theorems.Thm_Formalism_IndefR_DeterminantProjection_sigma_rowJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {K : Type*} [Field K] [CharZero K] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.IndefR.DeterminantProjection
theorem _root_.solution (σ : K →+* K) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n K) (hJ : ∀ i j, σ (J i j) = J j i)
    (hdet : J.det ≠ 0) [Nonempty n] : ∃ u : n → K, hsq σ J u ≠ 0 := by
  by_contra hcon
  push Not at hcon

  set B : (n → K) → (n → K) → K := fun u v => rowJ σ J u ⬝ᵥ v with hB
  have hadd : ∀ u v, hsq σ J (u + v) = hsq σ J u + hsq σ J v + B u v + B v u := by
    intro u v
    simp only [hsq, hB, rowJ, Pi.add_apply, map_add]
    rw [show (fun i => σ (u i) + σ (v i)) = (fun i => σ (u i)) + (fun i => σ (v i)) from rfl, add_vecMul,
      add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  have hsym : ∀ u v, B v u = σ (B u v) := by
    intro u v
    simp only [hB, dotProduct, map_sum, map_mul, sigma_rowJ σ hσ J hJ]
    simp only [rowJ, vecMul, mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hlin : ∀ u v (t : K), B u (t • v) = t * B u v := by
    intro u v t; simp only [hB, dotProduct_smul, smul_eq_mul]
  have hzero : ∀ u v, B u v = 0 := by
    intro u v
    have h0 : ∀ t : K, t * B u v + σ (t * B u v) = 0 := by
      intro t
      have := hadd u (t • v)
      rw [hcon, hcon, hcon, hsym u (t • v), hlin] at this
      linear_combination -this
    by_contra hb
    have := h0 (B u v)⁻¹
    rw [inv_mul_cancel₀ hb, map_one] at this
    norm_num at this
  apply hdet
  have hJ0 : J = 0 := by
    ext i j
    have := hzero (Pi.single i 1) (Pi.single j 1)
    simp only [hB, rowJ] at this
    rw [show (fun k => σ ((Pi.single i (1 : K) : n → K) k)) = Pi.single i 1 by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]] at this
    simpa [single_one_vecMul] using this
  rw [hJ0, Matrix.det_zero]
end Formalism.IndefR.DeterminantProjection
