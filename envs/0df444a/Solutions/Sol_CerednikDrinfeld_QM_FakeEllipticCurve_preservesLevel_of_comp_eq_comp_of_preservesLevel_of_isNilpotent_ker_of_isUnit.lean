-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_comp_eq_comp_of_preservesLevel_of_isNilpotent_ker_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/27566592-7a44-500c-aa28-5195df1c99ac

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_comp_eq_comp_of_preservesLevel_of_isNilpotent_ker_of_isUnit
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian"

namespace W2LevelLift

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_pow (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ]
    show L.mul t (nsmulPt L t n P) P = _
    rw [ih]; rfl

end W2LevelLift

open W2LevelLift in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

    {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p)) (hN : IsUnit ((N : ℕ) : S))
    (E A : FakeEllipticCurve Λ N S) (E₀ A₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia p E E₀ g)
    (gA : A₀.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia p A A₀ gA)

    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f)
    (φ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = A.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (φ₀ : E₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = E₀.f) (hred : g ≫ φ = φ₀ ≫ gA)
    (h₀ : FakeEllipticCurve.PreservesLevel E₀ A₀ φ₀ hφ₀) :
    FakeEllipticCurve.PreservesLevel E A φ hφ := by
  classical
  intro T t P hP
  obtain ⟨-, hiffA⟩ := FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit A hN
  refine (hiffA t (mapPt φ hφ P)).mpr ⟨?_, ?_⟩
  ·
    letI G : Group (SchemeHomOver t E.f) := E.L.pointGroup t
    letI G' : Group (SchemeHomOver t A.f) := A.L.pointGroup t
    let Φ : SchemeHomOver t E.f →* SchemeHomOver t A.f := MonoidHom.mk' (mapPt φ hφ) (fun x y => φ_mul t x y)
    have hNP : nsmulPt E.L t N P = E.L.one t := E.lev_torsion t P hP
    have h1 : P ^ N = 1 := by rw [← nsmulPt_eq_pow]; exact hNP
    have h2 : Φ P ^ N = 1 := by rw [← map_pow, h1, map_one]
    rw [nsmulPt_eq_pow]
    exact h2
  ·
    intro k _ _ sk τ hτ

    have hvan : ∀ x ∈ RingHom.ker p, sk x = 0 := by
      intro x hx
      obtain ⟨n, hn⟩ := hI
      have hxn : x ^ n = 0 := by
        have : x ^ n ∈ RingHom.ker p ^ n := Ideal.pow_mem_pow hx n
        rw [hn] at this
        simpa using this
      exact (IsNilpotent.map ⟨n, hxn⟩ sk).eq_zero
    let e := RingHom.quotientKerEquivOfSurjective hp
    let s₀ : S₀ →+* k := (Ideal.Quotient.lift (RingHom.ker p) sk hvan).comp e.symm.toRingHom
    have hs₀ : s₀.comp p = sk := by
      ext x
      show (Ideal.Quotient.lift (RingHom.ker p) sk hvan) (e.symm (p x)) = sk x
      have : e.symm (p x) = Ideal.Quotient.mk (RingHom.ker p) x := by
        apply e.injective
        rw [RingEquiv.apply_symm_apply]
        rfl
      rw [this, Ideal.Quotient.lift_mk]

    obtain ⟨hsq, -⟩ := id hg
    obtain ⟨P₁, hP₁⟩ := hP
    have hgeom : geomPoint k sk = Spec.map (CommRingCat.ofHom s₀) ≫ Spec.map (CommRingCat.ofHom p) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hs₀]; rfl
    have hcomm : (τ ≫ P.1) ≫ E.f = Spec.map (CommRingCat.ofHom s₀) ≫ Spec.map (CommRingCat.ofHom p) := by
      rw [Category.assoc, P.2, hτ, hgeom]
    set Q₀m : Spec (CommRingCat.of k) ⟶ E₀.A := hsq.lift (τ ≫ P.1) (Spec.map (CommRingCat.ofHom s₀)) hcomm with hQ₀m
    have hQ₀g : Q₀m ≫ g = τ ≫ P.1 := hsq.lift_fst _ _ _
    have hQ₀f : Q₀m ≫ E₀.f = Spec.map (CommRingCat.ofHom s₀) := hsq.lift_snd _ _ _
    let Q₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom s₀)) E₀.f := ⟨Q₀m, hQ₀f⟩
    have hQ₀lev : FactorsThrough E₀.lev Q₀ :=
      FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia E p E₀ g hg
        (Spec.map (CommRingCat.ofHom s₀)) Q₀ ⟨τ ≫ P₁, by rw [Category.assoc, hP₁, hQ₀g]⟩

    have hA₀ : FactorsThrough A₀.lev (mapPt φ₀ hφ₀ Q₀) := h₀ _ Q₀ hQ₀lev
    obtain ⟨-, -, -, hlevA⟩ := id hgA
    obtain ⟨R₀, hR₀⟩ := hlevA _ (mapPt φ₀ hφ₀ Q₀) hA₀
    refine ⟨R₀, ?_⟩
    rw [hR₀, mapPt_coe, schemeHomOverComp_coe, mapPt_coe]
    show (Q₀m ≫ φ₀) ≫ gA = τ ≫ P.1 ≫ φ
    rw [Category.assoc, ← hred, ← Category.assoc, hQ₀g, Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_comp_eq_comp_of_preservesLevel_of_isNilpotent_ker_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_comp_eq_comp_of_preservesLevel_of_isNilpotent_ker_of_isUnit (solution)
