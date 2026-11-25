-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.dbar_coordinates_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:45.867287+00:00
-- url     : https://prove2.me/submissions/98baea3a-8d70-4491-92ca-a2a38e668083

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_gamma_laws_hold

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
theorem _root_.solution : DbarCoord := by
  intro k _ n un D y z h a
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨g, hg⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * g := by rw [← hg]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, hcc0]
    simp
  have e2 : coeff 1 (X * z a) = constantCoeff (z a) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [← e2, h a]
  have hsm : ∀ v : Fin n → k⟦X⟧, ((X : k⟦X⟧) • D).mulVec v = (X : k⟦X⟧) • D.mulVec v := by
    intro v
    first
    | exact Matrix.smul_mulVec X D v
    | exact Matrix.smul_mulVec_assoc X D v
    | (funext i; simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
        Finset.mul_sum, mul_assoc])
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hsm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_add]
  rw [h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  first
  | (simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hcc0]; ring)
  | (simp only [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul, Matrix.map_apply, hcc0]; ring)
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
