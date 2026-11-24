-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.constantCoeff_conj_diagonal_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:20.367351+00:00
-- url     : https://prove2.me/submissions/2f409a2a-2fc6-4561-bf3c-4db4d494dc4c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution {L : Type} [Field L] {n : ℕ} (Γ G : Matrix (Fin n) (Fin n) L⟦X⟧) (υ : L)
    (a : Fin n → ℕ)
    (h : Γ * (G * Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)).map (rescale υ) =
      G * Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)) :
    Γ.map constantCoeff * G.map constantCoeff * Matrix.diagonal (fun j => υ ^ a j) =
      G.map constantCoeff := by
  have hr0 : ∀ f : L⟦X⟧, constantCoeff (rescale υ f) = constantCoeff f := fun f => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale,
      pow_zero, one_mul]
  have hD : (Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)).map (rescale υ) =
      Matrix.diagonal (fun j => C (υ ^ a j) * (X : L⟦X⟧) ^ a j) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext j
    simp only [map_pow, rescale_X, mul_pow]
  rw [Matrix.map_mul, hD, ← Matrix.mul_assoc] at h
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal] at hij
  have hX : (X : L⟦X⟧) ^ a j ≠ 0 := pow_ne_zero _ X_ne_zero
  have h2 : (Γ * G.map (rescale υ)) i j * C (υ ^ a j) = G i j := by
    apply mul_right_cancel₀ hX
    rw [mul_assoc, hij]
  have h3 := congrArg constantCoeff h2
  rw [map_mul, constantCoeff_C, Matrix.mul_apply, map_sum] at h3
  rw [Matrix.mul_diagonal, Matrix.map_apply, ← h3, Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, hr0]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
