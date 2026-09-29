-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isPullbackVia_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1887861d-de65-55eb-813a-632f95873305

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem solution
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hN : IsUnit ((N : ℕ) : 𝒪))
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E Ef : FakeEllipticCurve Λ N B}
    (q : E.A ⟶ Ef.A) (f₀ : A₀.A ⟶ A₀.A)
    (ρ : Rigidification r π A₀ ψ E) (ρf : Rigidification r π A₀ ψ Ef)
    (hcorr : ∃ (qb : ρ.Eb.A ⟶ ρf.Eb.A) (_ : qb ≫ ρf.gb = ρ.gb ≫ q) (_ : qb ≫ ρf.Eb.f = ρ.Eb.f)
      (uA : ρf.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (_ : uA ≫ ρ.gA = ρf.gA)
      (eb : ρ.Ab.A ⟶ ρ.Ab.A) (_ : eb ≫ ρ.gA = ρ.gA ≫ f₀) (_ : eb ≫ ρ.Ab.f = ρ.Ab.f)
      (i j : ℕ),
      qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ eb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    {L : Type} [CommRing L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L)
    {EL EfL : FakeEllipticCurve Λ N L}
    (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* L) E EL g)
    (gf : EfL.A ⟶ Ef.A) (hgf : FakeEllipticCurve.IsPullbackVia (φ : B →+* L) Ef EfL gf)
    (ρL : Rigidification r π A₀ (φ.comp ψ) EL) (ρfL : Rigidification r π A₀ (φ.comp ψ) EfL)
    (hρL : Rigidification.IsPullbackVia φ g hg ρ ρL) (hρfL : Rigidification.IsPullbackVia φ gf hgf ρf ρfL)
    (qL : EL.A ⟶ EfL.A) (hqL : qL ≫ gf = g ≫ q) (hqLf : qL ≫ EfL.f = EL.f) :
    ∃ (qb : ρL.Eb.A ⟶ ρfL.Eb.A) (_ : qb ≫ ρfL.gb = ρL.gb ≫ qL) (_ : qb ≫ ρfL.Eb.f = ρL.Eb.f)
      (uA : ρfL.Ab.A ⟶ ρL.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρL.Ab ρfL.Ab uA) (_ : uA ≫ ρL.gA = ρfL.gA)
      (eb : ρL.Ab.A ⟶ ρL.Ab.A) (_ : eb ≫ ρL.gA = ρL.gA ≫ f₀) (_ : eb ≫ ρL.Ab.f = ρL.Ab.f)
      (i j : ℕ),
      qb ≫ ρfL.φ ≫ uA ≫ ρL.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρL.φ ≫ eb ≫ ρL.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  obtain ⟨qb, hqb_gb, hqb_f, uA, huAPB, huA_gA, eb, heb_gA, heb_f, i, j, hij⟩ := hcorr

  obtain ⟨ub, uA₀, hubPB, hub_gb, huA₀PB, huA₀_gA, -, hφ⟩ := hρL
  obtain ⟨ubf, uAf₀, hubfPB, hubf_gb, huAf₀PB, huAf₀_gA, -, hφf⟩ := hρfL

  obtain ⟨hpbfEb, -, -, -⟩ := ρf.isPullback_Eb
  obtain ⟨hpbAb, -, -, -⟩ := ρ.isPullback_Ab
  obtain ⟨hpbuA, -, -, -⟩ := huAPB
  obtain ⟨hpbub, -, -, -⟩ := hubPB
  obtain ⟨hpbuA₀, -, hactuA₀, -⟩ := huA₀PB
  obtain ⟨hpbubf, -, -, -⟩ := hubfPB
  obtain ⟨hpbuAf₀, -, -, -⟩ := huAf₀PB
  obtain ⟨hpbfLEb, -, -, -⟩ := ρfL.isPullback_Eb
  obtain ⟨hpbg, -, -, -⟩ := hg
  have hSid : ∀ (R : Type) [CommRing R], Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _ := by
    intro R _
    exact Spec.map_id _

  have hNL : IsUnit ((N : ℕ) : L ⧸ Ideal.span {algebraMap 𝒪 L π}) := by
    simpa using hN.map ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})).comp (algebraMap 𝒪 L))

  have hwq : (ρL.gb ≫ qL) ≫ EfL.f = ρL.Eb.f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))) := by
    obtain ⟨hpbLEb, -, -, -⟩ := ρL.isPullback_Eb
    rw [Category.assoc, hqLf]; exact hpbLEb.w

  obtain ⟨uAL, huAL_gA, huAL_f, huALPB⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hNL A₀ ρL.Ab ρL.gA ρL.isPullback_Ab ρfL.Ab ρfL.gA ρfL.isPullback_Ab
  refine ⟨hpbfLEb.lift (ρL.gb ≫ qL) ρL.Eb.f hwq, hpbfLEb.lift_fst _ _ _, hpbfLEb.lift_snd _ _ _,
    uAL, huALPB, huAL_gA,
    hpbuA₀.lift (uA₀ ≫ eb) ρL.Ab.f (by rw [Category.assoc, heb_f]; exact hpbuA₀.w), ?_, ?_, i, j, ?_⟩
  ·
    rw [← huA₀_gA, ← Category.assoc, hpbuA₀.lift_fst, Category.assoc, heb_gA, Category.assoc]
  ·
    exact hpbuA₀.lift_snd _ _ _
  ·

    have hEb : hpbfLEb.lift (ρL.gb ≫ qL) ρL.Eb.f hwq ≫ ubf = ub ≫ qb := by
      apply hpbfEb.hom_ext
      · rw [Category.assoc, hubf_gb, ← Category.assoc, hpbfLEb.lift_fst, Category.assoc, hqL, Category.assoc, hqb_gb,
          ← Category.assoc, ← hub_gb, Category.assoc]
      · rw [Category.assoc, hpbubf.w, ← Category.assoc, hpbfLEb.lift_snd, Category.assoc, hqb_f, hpbub.w]

    have hAb : uAL ≫ uA₀ = uAf₀ ≫ uA := by
      apply hpbAb.hom_ext
      · rw [Category.assoc, huA₀_gA, huAL_gA, Category.assoc, huA_gA, huAf₀_gA]
      · rw [Category.assoc, hpbuA₀.w, ← Category.assoc, huAL_f, Category.assoc, hpbuA.w, hSid, Category.comp_id, hpbuAf₀.w]
    apply hpbuA₀.hom_ext
    ·
      simp only [Category.assoc, hactuA₀, IsPullback.lift_fst, IsPullback.lift_fst_assoc]
      rw [← Category.assoc uAL uA₀, hAb]
      simp only [Category.assoc]
      rw [← Category.assoc ρfL.φ uAf₀, ← hφf, ← Category.assoc ρL.φ uA₀, ← hφ]
      simp only [Category.assoc]
      rw [← Category.assoc (hpbfLEb.lift _ _ _) ubf, hEb, Category.assoc]
      congr 1 <;> exact hij
    ·
      simp only [Category.assoc]
      rw [ρL.Ab.act_over, ρL.Ab.act_over, hpbuA₀.lift_snd, ρL.φ_over, huAL_f, ρfL.φ_over, hpbfLEb.lift_snd]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia (solution)
