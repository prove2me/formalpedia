-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_mul_eq_algebraMap_and_maximalIdeal_eq_map_sup_span_pair_sup_sq_of_isProrepresentedBy_deformations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6e130427-d8db-55c0-b1d9-bf89a9b6f56b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
import Theorems.Thm_IsLocalRing_maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_mul_eq_algebraMap_and_maximalIdeal_eq_map_sup_span_pair_sup_sq_of_isProrepresentedBy_deformations
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    [IsAlgClosed (IsLocalRing.ResidueField Onr)]
    (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Onr R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
            (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
            resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
          ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries))
    (hnode₀ : (∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
    (hnode₁ : (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)) :
    ∃ u ∈ IsLocalRing.maximalIdeal R, ∃ v ∈ IsLocalRing.maximalIdeal R,
      u * v = algebraMap Onr R ((q : ℕ) : Onr) ∧
      IsLocalRing.maximalIdeal R = (IsLocalRing.maximalIdeal Onr).map (algebraMap Onr R) ⊔ Ideal.span {u, v} ⊔ (IsLocalRing.maximalIdeal R) ^ 2 := by
  classical
  obtain ⟨e₀, e₁, u, v, he₀, he₁, hbasis, hu, hv, huv, hum, hvm⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
      Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO hnode₀ hnode₁
  refine ⟨u, hum, v, hvm, huv, ?_⟩
  refine IsLocalRing.maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn Onr R resR hresR {u, v} ?_ ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [hum, hvm]
  · intro χ χ' hχ hχ' hs
    exact CerednikDrinfeld.SpecialFormalODModule.ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
      Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO hnode₀ hnode₁ e₀ e₁ u v he₀ he₁ hbasis hu hv
      χ χ' hχ hχ' (hs u (by simp)) (hs v (by simp))

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_exists_mul_eq_algebraMap_and_maximalIdeal_eq_map_sup_span_pair_sup_sq_of_isProrepresentedBy_deformations
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_mul_eq_algebraMap_and_maximalIdeal_eq_map_sup_span_pair_sup_sq_of_isProrepresentedBy_deformations (solution)
