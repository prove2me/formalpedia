-- Prove2me | solution 1 for FunctorialResolution.Blowup.exists_mul_pow_eq_chartRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:14:10.968804+00:00
-- url     : https://prove2.me/submissions/452a4183-39dc-4c35-a92a-f0c903fee1c2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_apply
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_coe_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply


section
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.Blowup
universe u
private theorem localization_mk_one_pow {A : Type u} [CommRing A] (S : Submonoid A) (x : A)
    (n : ℕ) :
    Localization.mk x (1 : S) ^ n = Localization.mk (x ^ n) (1 : S) := by
  rw [Localization.mk_one_eq_algebraMap, Localization.mk_one_eq_algebraMap, map_pow]
private theorem val_chartRingHom {R : Type u} [CommRing R] (I : Ideal R) (a : ↥I) (r : R) :
    (chartRingHom I a r).val =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesGrading I 0)) : ↥(reesAlgebra I))
        (1 : ↥(Submonoid.powers (reesGenerator I a))) := by
  rw [chartRingHom_apply]
  rfl
end FunctorialResolution.Blowup
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u
namespace FunctorialResolution.Blowup
theorem _root_.solution {R : Type u} [CommRing R] (I : Ideal R) (a : ↥I)
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :
    ∃ (n : ℕ) (r : R), z * chartRingHom I a (a : R) ^ n = chartRingHom I a r := by
  obtain ⟨k, hk⟩ := z.den_mem
  obtain ⟨s, hs, hnum⟩ := (mem_reesGrading_iff_monomial I z.deg z.num).mp z.num_mem_deg
  have hdencoe : ((z.den : ↥(reesAlgebra I)) : Polynomial R)
      = Polynomial.monomial k ((a : R) ^ k) := by
    rw [← hk]
    simp [reesGenerator_coe, Polynomial.monomial_pow]
  by_cases hik : z.deg = k
  · refine ⟨k, s, ?_⟩
    apply HomogeneousLocalization.val_injective
    have key : z.num * ((reesDegreeZeroEquiv I (a : R) : ↥(reesGrading I 0)) : ↥(reesAlgebra I)) ^ k
        = z.den * ((reesDegreeZeroEquiv I s : ↥(reesGrading I 0)) : ↥(reesAlgebra I)) := by
      apply Subtype.ext
      push_cast
      rw [hnum, hdencoe, hik, reesDegreeZeroEquiv_coe_coe, reesDegreeZeroEquiv_coe_coe,
        ← Polynomial.C_pow, ← Polynomial.monomial_zero_left, ← Polynomial.monomial_zero_left,
        Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial, mul_comm]
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      z.eq_num_div_den, val_chartRingHom, localization_mk_one_pow, Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simpa using key⟩
  · refine ⟨0, 0, ?_⟩
    apply HomogeneousLocalization.val_injective
    have hak : (a : R) ^ k = 0 := by
      have h0 := (mem_reesGrading_iff_coeff I z.deg z.den).mp z.den_mem_deg k (Ne.symm hik)
      rw [hdencoe] at h0
      simpa using h0
    have hden0 : (z.den : ↥(reesAlgebra I)) = 0 := by
      apply Subtype.ext
      rw [hdencoe, hak]
      simp
    have h0S : (0 : ↥(reesAlgebra I)) ∈ Submonoid.powers (reesGenerator I a) := ⟨k, hk.trans hden0⟩
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      z.eq_num_div_den, val_chartRingHom, localization_mk_one_pow, Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨⟨0, h0S⟩, by simp [hden0]⟩
end FunctorialResolution.Blowup
