-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8e01e8c3-d18d-58b7-8ae4-cbb8f9685235

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_eq_of_specMap_includeLeft_comp_eq_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq

set_option autoImplicit false

open scoped NumberField TensorProduct
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (m : ℕ) (hm : 0 < m)
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B]
    (hB : IsNilpotent (algebraMap 𝒪 B π))
    (T : Scheme.{0}) (f : Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⟶ T)
    (hf : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom) ≫ f = f) :
    ∃! g : Spec (CommRingCat.of B) ⟶ T,
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫ g = f := by
  obtain ⟨g, hg⟩ := CerednikDrinfeld.FormalOmega.exists_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq 𝒪 hdvr π hπ hcomplete
    hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B hB T f hf
  exact ⟨g, hg, fun g' hg' => CerednikDrinfeld.FormalOmega.eq_of_specMap_includeLeft_comp_eq_of_isNilpotent 𝒪 hdvr π hπ hcomplete
    hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B hB T g' g (hg'.trans hg.symm)⟩

end S_CerednikDrinfeld_FormalOmega_existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq (solution)
