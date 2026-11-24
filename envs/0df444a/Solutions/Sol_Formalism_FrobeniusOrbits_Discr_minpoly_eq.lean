-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.minpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:04.126645+00:00
-- url     : https://prove2.me/submissions/545a28b6-b5ab-4702-bb85-d3b4591c78aa

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_zeta_not_mem
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_th_coe
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    minpoly ℚ⟮z + z⁻¹⟯ z = X ^ 2 - C (th z) * X + 1 := by
  have hm : 2 ^ (e + 2) ≠ 0 := by positivity
  have hz0 : z ≠ 0 := hz.ne_zero hm
  have hq : (X ^ 2 - C (th z) * X + 1 : ℚ⟮z + z⁻¹⟯[X]).Monic := by monicity!
  have hev : aeval z (X ^ 2 - C (th z) * X + 1 : ℚ⟮z + z⁻¹⟯[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow, map_one]
    rw [IntermediateField.algebraMap_apply, th_coe, add_mul, inv_mul_cancel₀ hz0]
    ring
  have hdeg : (X ^ 2 - C (th z) * X + 1 : ℚ⟮z + z⁻¹⟯[X]).natDegree = 2 := by compute_degree!
  have hint := isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot hz
  have hmin2 : 2 ≤ (minpoly ℚ⟮z + z⁻¹⟯ z).natDegree := by
    have h0 := minpoly.natDegree_pos hint
    have h1 : (minpoly ℚ⟮z + z⁻¹⟯ z).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨y, hy⟩
      have h3 := y.2
      rw [show (y : K) = z from hy] at h3
      exact zeta_not_mem hz h3
    omega
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hq
    (minpoly.dvd _ _ hev) (by rw [hdeg]; exact hmin2)).symm
end Formalism.FrobeniusOrbits.Discr
