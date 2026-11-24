-- Prove2me | solution 1 for FunctorialResolution.Blowup.chartRingHom_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:42:24.966795+00:00
-- url     : https://prove2.me/submissions/b0f65667-ea4b-407d-8a32-54aadb85a066

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
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
private theorem localization_mk_eq_zero_iff {A : Type u} [CommRing A] {M : Submonoid A} (x : A)
    (s : ↥M) : Localization.mk x s = (0 : Localization M) ↔ ∃ c : ↥M, (c : A) * x = 0 := by
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_eq_zero_iff x s
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
theorem _root_.solution (I : Ideal R) (a : ↥I) :
    chartRingHom I a (a : R) ∈
      nonZeroDivisors (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) := by
  have key : ∀ z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a),
      chartRingHom I a (a : R) * z = 0 → z = 0 := by
    intro z hz
    have hz' : HomogeneousLocalization.val (chartRingHom I a (a : R) * z) = 0 := by
      rw [hz, HomogeneousLocalization.val_zero]
    rw [HomogeneousLocalization.val_mul, val_chartRingHom,
      HomogeneousLocalization.eq_num_div_den z, Localization.mk_mul,
      localization_mk_eq_zero_iff] at hz'
    obtain ⟨c, hc⟩ := hz'
    obtain ⟨m, hm⟩ : ∃ m : ℕ, reesGenerator I a ^ m = (c : ↥(reesAlgebra I)) := c.2
    rw [← hm] at hc
    have hP : reesGenerator I a ^ (m + 1) * HomogeneousLocalization.num z = 0 := by
      apply Subtype.ext
      have h1 := congrArg (fun p : ↥(reesAlgebra I) => (p : Polynomial R)) hc
      push_cast [reesGenerator_coe_eq_C_mul_X, reesDegreeZeroEquiv_coe_coe] at h1
      push_cast [reesGenerator_coe_eq_C_mul_X]
      linear_combination (Polynomial.X : Polynomial R) * h1
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_zero,
      HomogeneousLocalization.eq_num_div_den z, localization_mk_eq_zero_iff]
    exact ⟨⟨reesGenerator I a ^ (m + 1), Submonoid.pow_mem _ (Submonoid.mem_powers _) (m + 1)⟩, hP⟩
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun z hz => key z ((mul_comm (chartRingHom I a (a : R)) z).trans hz)⟩
end FunctorialResolution.Blowup
