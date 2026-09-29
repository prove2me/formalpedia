-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3c3af461-6df6-5ebd-9c12-8312fd50ad93

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_mumfordBundle_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation

open scoped Quaternion TensorProduct NumberField

open CategoryTheory.Limits in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁]
    [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B₁ B₀)))
    (hsmall : ∀ x ∈ RingHom.ker (algebraMap B₁ B₀), ∀ m ∈ maximalIdeal B₁, x * m = 0)
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (star : ↥Λ → ↥Λ)
    (𝓛₀ : E₀.A.Modules) (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hiso : Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀))
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by
  classical
  obtain ⟨hgc, hgmul, hgact, -⟩ := hg
  obtain ⟨e⟩ := hiso

  have hKtop : RingHom.ker (algebraMap B₁ B₀) ≠ ⊤ := by
    intro h
    obtain ⟨n, hn⟩ := hker
    rw [h, Ideal.top_pow, Ideal.zero_eq_bot] at hn
    exact (bot_ne_top (α := Ideal B₁)) hn.symm
  have hKle : RingHom.ker (algebraMap B₁ B₀) ≤ maximalIdeal B₁ := IsLocalRing.le_maximalIdeal hKtop
  have hK2 : RingHom.ker (algebraMap B₁ B₀) * RingHom.ker (algebraMap B₁ B₀) = ⊥ :=
    eq_bot_iff.mpr (Ideal.mul_le.mpr fun x hx y hy => by
      rw [Ideal.mem_bot]; exact hsmall x hx y (hKle hy))
  have hKm : maximalIdeal B₁ * RingHom.ker (algebraMap B₁ B₀) = ⊥ :=
    eq_bot_iff.mpr (Ideal.mul_le.mpr fun m hm x hx => by
      rw [Ideal.mem_bot, mul_comm]; exact hsmall x hx m hm)

  haveI : Nontrivial B₀ := by
    refine ⟨⟨0, 1, fun h => hKtop ?_⟩⟩
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    exact h.symm
  haveI : IsLocalRing B₀ := IsLocalRing.of_surjective' (algebraMap B₁ B₀) hπ

  have hΛ : Scheme.Modules.IsInvertible (mumfordBundle E.f E.L 𝓛) := by
    unfold mumfordBundle
    exact (h𝓛.pullback _).tensor_monoidalV2
      ((h𝓛.dual_monoidalV2.1.pullback _).tensor_monoidalV2 (h𝓛.dual_monoidalV2.1.pullback _))
  have hg𝓛 : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback g).obj 𝓛) := h𝓛.pullback g
  have h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀ := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hx, ⟨t⟩⟩ := hg𝓛.1 x
    exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ t⟩⟩

  have hacte : ∀ x : ↥Λ,
      (E.L.one (𝟙 (Spec (CommRingCat.of B₁)))).1 ≫ E.act x = (E.L.one (𝟙 (Spec (CommRingCat.of B₁)))).1 := by
    intro x
    letI G : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of B₁))) E.f) := E.L.pointGroup (𝟙 _)
    have hmul : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of B₁))) E.f, P * Q = E.L.mul _ P Q :=
      fun _ _ => rfl
    have h := E.act_hom x (𝟙 _) (E.L.one (𝟙 _)) (E.L.one (𝟙 _))
    rw [E.L.one_mul] at h
    have hoo : pushPt (E.act x) (E.act_over x) (E.L.one (𝟙 _)) * pushPt (E.act x) (E.act_over x) (E.L.one (𝟙 _)) =
        pushPt (E.act x) (E.act_over x) (E.L.one (𝟙 _)) * 1 := by
      rw [mul_one, hmul]; exact h.symm
    have h1 : pushPt (E.act x) (E.act_over x) (E.L.one (𝟙 _)) = 1 := mul_left_cancel hoo
    exact congrArg Subtype.val h1

  have eΛ₀ : mumfordBundle E₀.f E₀.L ((Scheme.Modules.pullback g).obj 𝓛) ≅ mumfordBundle E₀.f E₀.L 𝓛₀ :=
    ((locIsoOnBase_iff_nonempty_iso_of_isLocalRing _ _ _).mp
      (LocIsoOnBase.mumfordBundle_of_isInvertible E₀.f E₀.L hg𝓛 h𝓛₀
        ((locIsoOnBase_iff_nonempty_iso_of_isLocalRing _ _ _).mpr ⟨e⟩))).some
  obtain ⟨eBC⟩ := nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback B₁ B₀ (algebraMap B₁ B₀)
    E.f E.L E₀.f E₀.L g hgc hgmul 𝓛 h𝓛

  intro x
  refine (locIsoOnBase_iff_nonempty_iso_of_isLocalRing _ _ _).mpr ?_
  refine AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing hπ hK2 hKm
    E.L E.bundle E₀.L g hgc hgmul _ _ (hΛ.pullback _) (hΛ.pullback _) ?_ ?_ ?_ ?_ ?_
  ·

    have hsq₁ : pullback.lift (pullback.fst E₀.f E₀.f ≫ g) (pullback.snd E₀.f E₀.f ≫ g)
          (by rw [Category.assoc, Category.assoc, hgc.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫
        pullback.lift (pullback.fst E.f E.f) (pullback.snd E.f E.f ≫ E.act x)
          (by rw [Category.assoc, E.act_over]; exact pullback.condition) =
        pullback.lift (pullback.fst E₀.f E₀.f) (pullback.snd E₀.f E₀.f ≫ E₀.act x)
          (by rw [Category.assoc, E₀.act_over]; exact pullback.condition) ≫
        pullback.lift (pullback.fst E₀.f E₀.f ≫ g) (pullback.snd E₀.f E₀.f ≫ g)
          (by rw [Category.assoc, Category.assoc, hgc.w, ← Category.assoc, pullback.condition, Category.assoc]) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hgact]
    have hsq₂ : pullback.lift (pullback.fst E₀.f E₀.f ≫ g) (pullback.snd E₀.f E₀.f ≫ g)
          (by rw [Category.assoc, Category.assoc, hgc.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫
        pullback.lift (pullback.fst E.f E.f ≫ E.act (star x)) (pullback.snd E.f E.f)
          (by rw [Category.assoc, E.act_over]; exact pullback.condition) =
        pullback.lift (pullback.fst E₀.f E₀.f ≫ E₀.act (star x)) (pullback.snd E₀.f E₀.f)
          (by rw [Category.assoc, E₀.act_over]; exact pullback.condition) ≫
        pullback.lift (pullback.fst E₀.f E₀.f ≫ g) (pullback.snd E₀.f E₀.f ≫ g)
          (by rw [Category.assoc, Category.assoc, hgc.w, ← Category.assoc, pullback.condition, Category.assoc]) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hgact]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    obtain ⟨e₀⟩ := (locIsoOnBase_iff_nonempty_iso_of_isLocalRing _ _ _).mp (hR₀ x)
    refine ⟨?_⟩
    refine (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hsq₁).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (eBC.symm ≪≫ eΛ₀) ≪≫ e₀ ≪≫
      (Scheme.Modules.pullback _).mapIso (eΛ₀.symm ≪≫ eBC) ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hsq₂.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm
  · exact (AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq E.L E.bundle 𝓛 h𝓛
      (𝟙 _) (E.act x) (Category.id_comp _) (E.act_over x) (Category.comp_id _) (hacte x) _
      (by rw [pullback.lift_fst, Category.comp_id]) (pullback.lift_snd _ _ _)).1
  · exact (AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq E.L E.bundle 𝓛 h𝓛
      (𝟙 _) (E.act x) (Category.id_comp _) (E.act_over x) (Category.comp_id _) (hacte x) _
      (by rw [pullback.lift_fst, Category.comp_id]) (pullback.lift_snd _ _ _)).2
  · exact (AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq E.L E.bundle 𝓛 h𝓛
      (E.act (star x)) (𝟙 _) (E.act_over (star x)) (Category.id_comp _) (hacte (star x)) (Category.comp_id _) _
      (pullback.lift_fst _ _ _) (by rw [pullback.lift_snd, Category.comp_id])).1
  · exact (AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq E.L E.bundle 𝓛 h𝓛
      (E.act (star x)) (𝟙 _) (E.act_over (star x)) (Category.id_comp _) (hacte (star x)) (Category.comp_id _) _
      (pullback.lift_fst _ _ _) (by rw [pullback.lift_snd, Category.comp_id])).2

end S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing (solution)
