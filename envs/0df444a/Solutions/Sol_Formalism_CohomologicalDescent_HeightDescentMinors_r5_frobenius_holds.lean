-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r5_frobenius_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:34.125299+00:00
-- url     : https://prove2.me/submissions/63a5ef95-2912-48f6-93ce-28000f33c57e

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_subst_powerSeries
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_one_add_X_pow_sub_one_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_X_pow_of_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_pow_prime_eq_subst_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_eq_C_prime_mul_of_map_toZMod_zero

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : FrobeniusCongruence := by
  intro l _ f
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hX : HasSubst (X ^ l : (ZMod l)⟦X⟧) := hasSubst_X_pow_of_ne_zero hl
  have h1 : PowerSeries.map (PadicInt.toZMod (p := l)) ((1 + X) ^ l - 1 : ℤ_[l]⟦X⟧) = X ^ l := by
    simp only [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
    rw [pow_prime_eq_subst_X_pow, ← PowerSeries.coe_substAlgHom hX, map_add, map_one,
      PowerSeries.substAlgHom_X]
    ring
  have key : PowerSeries.map (PadicInt.toZMod (p := l)) (phi l ℤ_[l] f - f ^ l) = 0 := by
    rw [map_sub, map_pow, phi, map_subst_powerSeries _ (hasSubst_one_add_X_pow_sub_one_alt l), pow_prime_eq_subst_X_pow, h1,
      sub_self]
  obtain ⟨r, hr⟩ := exists_eq_C_prime_mul_of_map_toZMod_zero l _ key
  exact ⟨r, by rw [← hr]; ring⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
