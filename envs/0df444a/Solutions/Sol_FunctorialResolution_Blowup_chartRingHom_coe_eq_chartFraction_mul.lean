-- Prove2me | solution 1 for FunctorialResolution.Blowup.chartRingHom_coe_eq_chartFraction_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:58:53.792209+00:00
-- url     : https://prove2.me/submissions/3657b09e-681e-48ba-a7ed-d1193cd62d8f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Theorems.Thm_FunctorialResolution_Blowup_chartFraction_eq_mk
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_coe_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
private theorem reesGenerator_coe_eq_C_mul_X (I : Ideal R) (a : ↥I) :
    ((reesGenerator I a : ↥(reesAlgebra I)) : Polynomial R) =
      Polynomial.C (a : R) * Polynomial.X := by
  rw [reesGenerator_coe, ← Polynomial.C_mul_X_pow_eq_monomial, pow_one]
namespace AffineBlowup
end AffineBlowup
private theorem val_chartRingHom (I : Ideal R) (a : ↥I) (r : R) :
    HomogeneousLocalization.val (chartRingHom I a r) =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)))
        (1 : ↥(Submonoid.powers (reesGenerator I a))) := rfl
end FunctorialResolution.Blowup
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (a b : ↥I) :
    chartRingHom I a (b : R) = chartFraction I a b * chartRingHom I a (a : R) := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    val_chartRingHom, val_chartRingHom, chartFraction_eq_mk, HomogeneousLocalization.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [reesGenerator_coe_eq_C_mul_X, reesDegreeZeroEquiv_coe_coe]
  ring
end FunctorialResolution.Blowup
