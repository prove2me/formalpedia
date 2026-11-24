-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.closure_chartRingHom_union_chartFraction_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:28:08.265183+00:00
-- url     : https://prove2.me/submissions/1afd4400-ffe5-4ce9-86b7-5da516b56120

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_apply
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_coe_eq_chartFraction_mul
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_mem_nonZeroDivisors
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
universe u
section
variable {B A : Type u} [CommRing B] [CommRing A]
end
private theorem eq_mul_pow_zero {M : Type u} [CommRing M] (x c : M) : x = x * c ^ 0 := by ring
private theorem mul_add_mul_eq_add_mul {M : Type u} [CommRing M] (x y c : M) :
    x * c + y * c = (x + y) * c := by ring
private theorem self_sub_self_eq_zero {M : Type u} [CommRing M] (x : M) : x - x = 0 := by ring
private theorem localization_mk_eq_mk_one_of_eq_mul {M : Type u} [CommMonoid M] {S : Submonoid M}
    (x y d : M) (hd : d ∈ S) (h : x = d * y) :
    Localization.mk x ⟨d, hd⟩ = Localization.mk y (1 : ↥S) := by
  rw [Localization.mk_eq_mk_iff]
  refine Localization.r_of_eq ?_
  simp [h]
section
variable {R : Type u} [CommRing R]
private theorem val_chartRingHom (I : Ideal R) (a : I) (t : R) :
    HomogeneousLocalization.val (Blowup.chartRingHom I a t)
      = Localization.mk (↑(Blowup.reesDegreeZeroEquiv I t) : ↥(reesAlgebra I))
          (1 : ↥(Submonoid.powers (Blowup.reesGenerator I a))) := by
  rw [Blowup.chartRingHom_apply]
  rfl
private theorem exists_pow_mul_eq (I : Ideal R) (a : I)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    ∃ (n : ℕ) (r : R), r ∈ I ^ n ∧
      z * Blowup.chartRingHom I a (a : R) ^ n = Blowup.chartRingHom I a r := by
  obtain ⟨m, hm⟩ := HomogeneousLocalization.den_mem z
  have hden : HomogeneousLocalization.den z = Blowup.reesGenerator I a ^ m := hm.symm
  have hdencoe : ((HomogeneousLocalization.den z : ↥(reesAlgebra I)) : Polynomial R)
      = Polynomial.monomial m ((a : R) ^ m) := by
    rw [hden, SubmonoidClass.coe_pow, Blowup.reesGenerator_coe, Polynomial.monomial_pow, one_mul]
  have hpow : (Blowup.chartRingHom I a) ((a : R) ^ m) = (Blowup.chartRingHom I a) (a : R) ^ m :=
    map_pow (Blowup.chartRingHom I a) (a : R) m
  by_cases hdeg : HomogeneousLocalization.deg z = m
  · have hnum : HomogeneousLocalization.num z ∈ Blowup.reesGrading I m := by
      rw [← hdeg]
      exact HomogeneousLocalization.num_mem_deg z
    obtain ⟨s, hs, hseq⟩ :=
      (Blowup.mem_reesGrading_iff_monomial I m (HomogeneousLocalization.num z)).mp hnum
    refine ⟨m, s, hs, ?_⟩
    have key : (HomogeneousLocalization.num z)
          * (↑(Blowup.reesDegreeZeroEquiv I ((a : R) ^ m)) : ↥(reesAlgebra I))
        = (HomogeneousLocalization.den z) * (↑(Blowup.reesDegreeZeroEquiv I s) : ↥(reesAlgebra I)) := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, hseq, hdencoe, Blowup.reesDegreeZeroEquiv_coe_coe]
      rw [mul_comm (Polynomial.monomial m s) (Polynomial.C ((a : R) ^ m)),
        Polynomial.C_mul_monomial,
        mul_comm (Polynomial.monomial m ((a : R) ^ m)) (Polynomial.C s),
        Polynomial.C_mul_monomial, mul_comm ((a : R) ^ m) s]
    rw [← hpow]
    apply HomogeneousLocalization.val_injective (Submonoid.powers (Blowup.reesGenerator I a))
    rw [HomogeneousLocalization.val_mul, val_chartRingHom, val_chartRingHom,
      HomogeneousLocalization.eq_num_div_den z, Localization.mk_mul, mul_one]
    exact localization_mk_eq_mk_one_of_eq_mul _ _ _ _ key
  · have hzero : (a : R) ^ m = 0 := by
      have h1 := (Blowup.mem_reesGrading_iff_coeff I (HomogeneousLocalization.deg z)
        (HomogeneousLocalization.den z)).mp (HomogeneousLocalization.den_mem_deg z) m
        (fun h => hdeg h.symm)
      rw [hdencoe] at h1
      simpa using h1
    refine ⟨m, 0, Ideal.zero_mem _, ?_⟩
    rw [← hpow, hzero, map_zero]
    exact mul_zero z
private theorem exists_mem_closure_chartRingHom_eq_mul_pow (I : Ideal R) (a : I) (n : ℕ) :
    ∀ r ∈ I ^ n, ∃ w ∈ Subring.closure
        (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a)),
      Blowup.chartRingHom I a r = w * Blowup.chartRingHom I a (a : R) ^ n := by
  induction n with
  | zero =>
    intro r _
    refine ⟨Blowup.chartRingHom I a r, Subring.subset_closure (Or.inl ⟨r, rfl⟩), ?_⟩
    exact eq_mul_pow_zero (M := HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) _ _
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro s hs b hb
      obtain ⟨w, hw, hweq⟩ := ih s hs
      have hbb : Blowup.chartRingHom I a b
          = Blowup.chartFraction I a ⟨b, hb⟩ * Blowup.chartRingHom I a (a : R) :=
        Blowup.chartRingHom_coe_eq_chartFraction_mul I a ⟨b, hb⟩
      refine ⟨w * Blowup.chartFraction I a ⟨b, hb⟩,
        Subring.mul_mem _ hw (Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, rfl⟩)), ?_⟩
      rw [map_mul, hweq, hbb]
      ring
    · rintro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
      refine ⟨wx + wy, Subring.add_mem _ hwx hwy, ?_⟩
      rw [map_add, hx, hy]
      exact mul_add_mul_eq_add_mul wx wy _
end
section
variable {R : Type u} [CommRing R]
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : Ideal R) (a : I) :
    Subring.closure
        (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a)) = ⊤ := by
  rw [Subring.eq_top_iff']
  intro z
  obtain ⟨n, r, hr, hz⟩ := exists_pow_mul_eq I a z
  obtain ⟨w, hw, hweq⟩ := exists_mem_closure_chartRingHom_eq_mul_pow I a n r hr
  have e1 : (z - w) * Blowup.chartRingHom I a (a : R) ^ n
      = z * Blowup.chartRingHom I a (a : R) ^ n - w * Blowup.chartRingHom I a (a : R) ^ n :=
    sub_mul z w _
  have h0 : (z - w) * Blowup.chartRingHom I a (a : R) ^ n = 0 := by
    rw [e1, hz, ← hweq]
    exact self_sub_self_eq_zero
      (M := HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) _
  have hnzd : Blowup.chartRingHom I a (a : R) ^ n
      ∈ nonZeroDivisors (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :=
    pow_mem (Blowup.chartRingHom_mem_nonZeroDivisors I a) n
  have hzw : z - w = 0 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  have hzeq : z = w := sub_eq_zero.mp hzw
  rw [hzeq]
  exact hw
end FunctorialResolution.EmbeddedResolution
