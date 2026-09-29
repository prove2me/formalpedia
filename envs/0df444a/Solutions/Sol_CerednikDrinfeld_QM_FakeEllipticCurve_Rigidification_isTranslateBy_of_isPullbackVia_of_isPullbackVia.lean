-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslateBy_of_isPullbackVia_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a84ebd9d-de95-55b3-9bf5-3a287b00dc42

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslateBy_of_isPullbackVia_of_isPullbackVia
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem solution
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hN : IsUnit ((N : ℕ) : 𝒪))
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (f : A₀.A ⟶ A₀.A) (ρ ρ' : Rigidification r π A₀ ψ E)
    (htr : Rigidification.IsTranslateBy hΛℤ f ρ ρ')
    {L : Type} [CommRing L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L)
    {EL : FakeEllipticCurve Λ N L} (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* L) E EL g)
    (ρL ρL' : Rigidification r π A₀ (φ.comp ψ) EL)
    (hρL : Rigidification.IsPullbackVia φ g hg ρ ρL) (hρL' : Rigidification.IsPullbackVia φ g hg ρ' ρL') :
    Rigidification.IsTranslateBy hΛℤ f ρL ρL' := by
  classical

  obtain ⟨u, uA, ⟨huPB, hu_gb, huAPB, huA_gA⟩, eγb, heγb_gA, heγb_f, i, j, hij⟩ := htr

  obtain ⟨ub, uA₀, hubPB, hub_gb, huA₀PB, huA₀_gA, -, hφ⟩ := hρL
  obtain ⟨ub', uA₀', hub'PB, hub'_gb, huA₀'PB, huA₀'_gA, -, hφ'⟩ := hρL'

  obtain ⟨hpbEb, -, -, -⟩ := ρ.isPullback_Eb
  obtain ⟨hpbAb, -, -, -⟩ := ρ.isPullback_Ab
  obtain ⟨hpbu, -, -, -⟩ := huPB
  obtain ⟨hpbuA, -, -, -⟩ := huAPB
  obtain ⟨hpbub, -, -, -⟩ := hubPB
  obtain ⟨hpbuA₀, -, hactuA₀, -⟩ := huA₀PB
  obtain ⟨hpbub', -, -, -⟩ := hub'PB
  obtain ⟨hpbuA₀', -, -, -⟩ := huA₀'PB
  have hSid : ∀ (R : Type) [CommRing R], Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _ := by
    intro R _
    exact Spec.map_id _

  have hNL : IsUnit ((N : ℕ) : L ⧸ Ideal.span {algebraMap 𝒪 L π}) := by
    simpa using hN.map ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})).comp (algebraMap 𝒪 L))

  obtain ⟨uL, huL_gb, huL_f, huLPB⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})) hNL EL ρL.Eb ρL.gb ρL.isPullback_Eb ρL'.Eb ρL'.gb ρL'.isPullback_Eb
  obtain ⟨uAL, huAL_gA, huAL_f, huALPB⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hNL A₀ ρL.Ab ρL.gA ρL.isPullback_Ab ρL'.Ab ρL'.gA ρL'.isPullback_Ab

  refine ⟨uL, uAL, ⟨huLPB, huL_gb, huALPB, huAL_gA⟩,
    hpbuA₀.lift (uA₀ ≫ eγb) ρL.Ab.f (by rw [Category.assoc, heγb_f]; exact hpbuA₀.w), ?_, ?_, i, j, ?_⟩
  ·
    rw [← huA₀_gA, ← Category.assoc, hpbuA₀.lift_fst, Category.assoc, heγb_gA, Category.assoc]
  ·
    exact hpbuA₀.lift_snd _ _ _
  ·

    have hEb : uL ≫ ub = ub' ≫ u := by
      apply hpbEb.hom_ext
      · rw [Category.assoc, hub_gb, ← Category.assoc, huL_gb, Category.assoc, hu_gb, hub'_gb]
      · rw [Category.assoc, hpbub.w, ← Category.assoc, huL_f, Category.assoc, hpbu.w, hSid, Category.comp_id, hpbub'.w]

    have hAb : uAL ≫ uA₀ = uA₀' ≫ uA := by
      apply hpbAb.hom_ext
      · rw [Category.assoc, huA₀_gA, huAL_gA, Category.assoc, huA_gA, huA₀'_gA]
      · rw [Category.assoc, hpbuA₀.w, ← Category.assoc, huAL_f, Category.assoc, hpbuA.w, hSid, Category.comp_id, hpbuA₀'.w]
    apply hpbuA₀.hom_ext
    ·
      simp only [Category.assoc]
      rw [hactuA₀, ← Category.assoc (hpbuA₀.lift _ _ _), hpbuA₀.lift_fst, hactuA₀]

      rw [← Category.assoc uAL uA₀, hAb]
      simp only [Category.assoc]
      rw [← Category.assoc ρL.φ uA₀, ← hφ, ← Category.assoc ρL'.φ uA₀', ← hφ']
      simp only [Category.assoc]
      rw [← Category.assoc uL ub, hEb, Category.assoc]
      congr 1
    ·
      simp only [Category.assoc]
      rw [ρL.Ab.act_over, ρL.Ab.act_over, hpbuA₀.lift_snd, ρL.φ_over, huL_f, huAL_f, ρL'.φ_over]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslateBy_of_isPullbackVia_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslateBy_of_isPullbackVia_of_isPullbackVia (solution)
