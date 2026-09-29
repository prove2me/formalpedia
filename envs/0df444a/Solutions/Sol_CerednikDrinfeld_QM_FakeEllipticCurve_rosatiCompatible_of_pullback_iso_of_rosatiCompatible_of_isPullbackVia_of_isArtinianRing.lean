-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a761b6d4-c871-5f6f-b15b-880adc4f3dfd

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation

open scoped Quaternion TensorProduct NumberField

namespace RosatiPersistReduce

open CerednikDrinfeld.QM.FakeEllipticCurve

theorem induct {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (star : ↥Λ → ↥Λ) (n : ℕ) :
    ∀ (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁] [CommRing B₀] [Algebra B₁ B₀],
      Function.Surjective (algebraMap B₁ B₀) →
      maximalIdeal B₁ ^ n * RingHom.ker (algebraMap B₁ B₀) = ⊥ →
      IsNilpotent (RingHom.ker (algebraMap B₁ B₀)) →
      ∀ (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A),
        FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g →
        ∀ (𝓛₀ : E₀.A.Modules) (𝓛 : E.A.Modules), Scheme.Modules.IsInvertible 𝓛 →
          Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀) →
          RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star →
          RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by
  induction n with
  | zero =>
    intro B₁ B₀ _ _ _ _ _ hπ hK hker E E₀ g hg 𝓛₀ 𝓛 h𝓛 hiso hR₀
    rw [pow_zero, one_mul] at hK
    refine rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
      B₁ B₀ hπ hker ?_ E E₀ g hg star 𝓛₀ 𝓛 h𝓛 hiso hR₀
    intro x hx m _
    rw [hK] at hx
    rw [(Submodule.mem_bot B₁).mp hx, zero_mul]
  | succ n ih =>
    intro B₁ B₀ _ _ _ _ _ hπ hK hker E E₀ g hg 𝓛₀ 𝓛 h𝓛 hiso hR₀

    set K : Ideal B₁ := RingHom.ker (algebraMap B₁ B₀) with hKdef
    let J : Ideal B₁ := maximalIdeal B₁ * K
    have hJK : J ≤ K := Ideal.mul_le_right
    have hJK' : ∀ x ∈ J, algebraMap B₁ B₀ x = 0 := fun x hx => by
      have := hJK hx
      rwa [hKdef, RingHom.mem_ker] at this
    have hJm : J ≤ maximalIdeal B₁ := Ideal.mul_le_left
    have hJtop : J ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal B₁).ne_top (top_le_iff.mp (h ▸ hJm))
    obtain ⟨E', g₁, g₀, hg₁, hg₀, hcomp⟩ :=
      exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker B₁ B₀ E E₀ g hg J hJK'

    haveI : Nontrivial (B₁ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
    haveI : IsLocalRing (B₁ ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk J) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    letI alg : Algebra (B₁ ⧸ J) B₀ := (Ideal.Quotient.lift J (algebraMap B₁ B₀) hJK').toAlgebra
    have halg : algebraMap (B₁ ⧸ J) B₀ = Ideal.Quotient.lift J (algebraMap B₁ B₀) hJK' := rfl

    have hπ' : Function.Surjective (algebraMap (B₁ ⧸ J) B₀) := by
      intro y
      obtain ⟨x, rfl⟩ := hπ y
      exact ⟨Ideal.Quotient.mk J x, by rw [halg, Ideal.Quotient.lift_mk]⟩
    have hker_le : RingHom.ker (algebraMap (B₁ ⧸ J) B₀) ≤ K.map (Ideal.Quotient.mk J) := by
      intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.mem_ker, halg, Ideal.Quotient.lift_mk] at hx
      refine Ideal.mem_map_of_mem _ ?_
      rw [hKdef, RingHom.mem_ker]
      exact hx
    have hsmall' : ∀ x ∈ RingHom.ker (algebraMap (B₁ ⧸ J) B₀),
        ∀ m ∈ maximalIdeal (B₁ ⧸ J), x * m = 0 := by
      intro x hx m hm
      obtain ⟨x', hx', rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hker_le hx)
      obtain ⟨m', rfl⟩ := Ideal.Quotient.mk_surjective m
      have hm' : m' ∈ maximalIdeal B₁ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
        exact fun hu => hm (hu.map _)
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, mul_comm]
      exact Ideal.mul_mem_mul hm' hx'
    have hker' : IsNilpotent (RingHom.ker (algebraMap (B₁ ⧸ J) B₀)) := by
      obtain ⟨m, hm⟩ := hker
      rw [Ideal.zero_eq_bot] at hm
      refine ⟨m, ?_⟩
      rw [Ideal.zero_eq_bot, ← le_bot_iff]
      calc RingHom.ker (algebraMap (B₁ ⧸ J) B₀) ^ m ≤ (K.map (Ideal.Quotient.mk J)) ^ m :=
            Ideal.pow_right_mono hker_le m
        _ = (K ^ m).map (Ideal.Quotient.mk J) := (Ideal.map_pow _ _ _).symm
        _ = ⊥ := by rw [hm, Ideal.map_bot]
    have hg₀' : FakeEllipticCurve.IsPullbackVia (algebraMap (B₁ ⧸ J) B₀) E' E₀ g₀ := hg₀
    obtain ⟨e⟩ := hiso
    let 𝓛' : E'.A.Modules := (Scheme.Modules.pullback g₁).obj 𝓛
    have h𝓛' : Scheme.Modules.IsInvertible 𝓛' := Scheme.Modules.IsInvertible.pullback g₁ h𝓛
    have e' : (Scheme.Modules.pullback g₀).obj 𝓛' ≅ 𝓛₀ :=
      (Scheme.Modules.pullbackComp g₀ g₁).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hcomp).app 𝓛 ≪≫ e
    have hR' : RosatiCompatible E'.f E'.L 𝓛' E'.act E'.act_over star :=
      rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
        (B₁ ⧸ J) B₀ hπ' hker' hsmall' E' E₀ g₀ hg₀' star 𝓛₀ 𝓛' h𝓛' ⟨e'⟩ hR₀

    have hKJ : RingHom.ker (algebraMap B₁ (B₁ ⧸ J)) = J := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    have hK₁ : maximalIdeal B₁ ^ n * RingHom.ker (algebraMap B₁ (B₁ ⧸ J)) = ⊥ := by
      rw [hKJ]
      change maximalIdeal B₁ ^ n * (maximalIdeal B₁ * K) = ⊥
      rw [← mul_assoc, ← pow_succ, hK]
    have hkerJ : IsNilpotent (RingHom.ker (algebraMap B₁ (B₁ ⧸ J))) := by
      rw [hKJ]
      obtain ⟨m, hm⟩ := hker
      rw [Ideal.zero_eq_bot] at hm
      refine ⟨m, ?_⟩
      rw [Ideal.zero_eq_bot, ← le_bot_iff, ← hm]
      exact Ideal.pow_right_mono hJK m
    have hg₁' : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ (B₁ ⧸ J)) E E' g₁ := by
      rw [Ideal.Quotient.algebraMap_eq]; exact hg₁
    exact ih B₁ (B₁ ⧸ J) Ideal.Quotient.mk_surjective hK₁ hkerJ E E' g₁ hg₁' 𝓛' 𝓛 h𝓛 ⟨Iso.refl _⟩ hR'

end RosatiPersistReduce

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁]
    [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B₁ B₀)))
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (star : ↥Λ → ↥Λ)
    (𝓛₀ : E₀.A.Modules) (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hiso : Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀))
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by
  classical
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B₁)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.zero_eq_bot] at hn
  refine RosatiPersistReduce.induct star n B₁ B₀ hπ ?_ hker E E₀ g hg 𝓛₀ 𝓛 h𝓛 hiso hR₀
  rw [hn, Ideal.bot_mul]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing (solution)
