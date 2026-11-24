-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.blockTriangular_of_mul_eq_pow_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:41.990213+00:00
-- url     : https://prove2.me/submissions/82719510-a956-4133-9191-9172e565be88

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (π : R) (n h : ℕ)
    (Φ Φ' : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (hπ : π ≠ 0) (hΦ : Φ.BlockTriangular b)
    (hm : Φ * Φ' = (π ^ h) • (1 : Matrix (Fin n) (Fin n) R)) : Φ'.BlockTriangular b := by
  intro i j hij
  let φ := algebraMap R (FractionRing R)
  have hinj : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hm' : Φ.map φ * Φ'.map φ = (φ π ^ h) • (1 : Matrix (Fin n) (Fin n) (FractionRing R)) := by
    rw [← Matrix.map_mul, hm]
    ext a c
    by_cases hac : a = c <;> simp [hac, Matrix.one_apply]
  have hc : (φ π) ^ h ≠ 0 := pow_ne_zero _ ((map_ne_zero_iff φ hinj).2 hπ)
  have hr : Φ.map φ * (((φ π) ^ h)⁻¹ • Φ'.map φ) = 1 := by
    rw [Matrix.mul_smul, hm', smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hinv : (Φ.map φ)⁻¹ = ((φ π) ^ h)⁻¹ • Φ'.map φ := Matrix.inv_eq_right_inv hr
  letI : Invertible (Φ.map φ) := by
    first
    | exact ⟨_, mul_eq_one_comm.mp hr, hr⟩
    | exact Matrix.invertibleOfIsUnitDet _ (Matrix.isUnit_det_of_right_inverse hr)
    | exact Matrix.invertibleOfRightInverse _ _ hr
  have hΦK : (Φ.map φ).BlockTriangular b := fun a c hac => by simp [hΦ hac]
  have h4 := Matrix.blockTriangular_inv_of_blockTriangular hΦK hij
  rw [hinv, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_eq_zero] at h4
  rcases h4 with h5 | h5
  · exact absurd h5 (inv_ne_zero hc)
  · exact hinj (by rw [h5, map_zero])
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
