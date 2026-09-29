-- Prove2me | solution 1 for CerednikDrinfeld.forall_exists_adicPoint_and_theta_eq_iff_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a685ad73-0814-5ac7-97e7-34b361358852

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Theorems.Thm_CerednikDrinfeld_exists_formalQuotientDatum_coeff_adicFib
import Theorems.Thm_CerednikDrinfeld_FormalQuotientDatum_exists_hom_pullback_comp_eq_theta_of_cerednikDrinfeld_quotient
import Theorems.Thm_CerednikDrinfeld_FormalQuotientDatum_isIso_of_isPullback_of_cerednikDrinfeld_quotient
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_forall_exists_adicPoint_and_theta_eq_iff_of_cerednikDrinfeld_quotient
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀ AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.smulHom_apply CerednikDrinfeld.Mumford.smulHom_mapDart CerednikDrinfeld.Mumford.walkCycle_nil LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪)) [IsProper f] [Flat f]

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘfib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
      (∀ y : (Scheme.nilpPoints f).obj k, ∃ P : (Omega K₀ π).obj k, Θ k hk (ψ, P) = y) ∧
      ∀ P P' : (Omega K₀ π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
        ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P'))
    (hΘuniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
          u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (Θ B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
            u' B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (Θ B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f).obj B),
            u' B hB y = u B hB y)

    {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    [CompleteSpace C] [IsAlgClosed C]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R)
    (ψ₀ : Onr →ₐ[𝒪] R) :

    (∀ p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R}, ∃ x : AdicPoint K₀ π R, ∀ n : ℕ,
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ p.1 =
          (Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1) ∧

    (∀ x x' : AdicPoint K₀ π R,
      (∀ n : ℕ, Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) =
          Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n)) ↔
      ∃ γ ∈ Γ, ∀ n : ℕ, OmegaNr.IsTwistedAct π Onr Fr vdet (modPow π R n) (σ γ)
          (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n)) := by
  classical
  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : IsAdicComplete (Ideal.span {π}) 𝒪 := hcomplete

  have hπ0 : algebraMap 𝒪 K₀ π ≠ 0 := fun h =>
    hπ.ne_zero ((IsFractionRing.injective 𝒪 K₀) (by rw [h, map_zero]))
  have hdet : (Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1]).det ≠ 0 := by
    rw [Matrix.det_diagonal]; simp [hπ0]
  let g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1] := rfl

  obtain ⟨D, -, hadic⟩ := CerednikDrinfeld.exists_formalQuotientDatum_coeff_adicFib 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr
    hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt g₁ hg₁

  let sR : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪) := fun n =>
    Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
  have hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) := fun n => rfl
  have hle : ∀ n : ℕ, Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)} := fun n =>
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))
  let tR : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})) :=
    fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hle n)))
  have htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n := by
    intro n
    simp only [sR, tR, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)) := fun n =>
    Limits.pullback.lift (Limits.pullback.fst f (sR n)) (Limits.pullback.snd f (sR n) ≫ tR n)
      (by rw [Category.assoc, htR, Limits.pullback.condition])
  have hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n) := fun n =>
    Limits.pullback.lift_fst _ _ _
  have hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n := fun n =>
    Limits.pullback.lift_snd _ _ _

  obtain ⟨v, hv_over, hv_sq, hv_q, hv_inj⟩ :=
    CerednikDrinfeld.FormalQuotientDatum.exists_hom_pullback_comp_eq_theta_of_cerednikDrinfeld_quotient 𝒪 hdvr π hπ hcomplete hres hunr
      K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' 𝒳 f Θ hΘnat hΘinv hΘfib g₁ D
      sR hsR tR htR xn hxn₁ hxn₂

  haveI : ∀ n : ℕ, IsProper (v n ≫ Limits.pullback.snd f (sR n)) := fun n => by rw [hv_over]; exact D.yb_isProper n
  obtain ⟨-, Yf, Gf, -, φ, hφ, hφt⟩ :=
    AlgebraicGeometry.exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete 𝒪 π 𝒳 f sR hsR tR htR xn hxn₁ hxn₂
      D.Y v D.yt hv_sq hv_inj
  have hviso : ∀ n : ℕ, IsIso (v n) :=
    CerednikDrinfeld.FormalQuotientDatum.isIso_of_isPullback_of_cerednikDrinfeld_quotient 𝒪 π K₀ Onr Fr vdet G σ Γ Γ' 𝒳 f Θ hΘnat hΘinv
      hΘuniv g₁ D sR hsR tR htR xn hxn₁ hxn₂ v hv_over hv_sq hv_q Yf Gf φ hφ hφt
  haveI : ∀ n : ℕ, IsIso (v n) := hviso

  have hmod : ∀ n : ℕ, (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1) = 0 := by
    intro n
    rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n), Ideal.Quotient.algebraMap_eq, map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨hsurjD, hfibD⟩ := hadic C Γ₀ R ϖ hF ψ₀ hmod

  have hcomap : ∀ n : ℕ, Ideal.span {π ^ (n + 1)} ≤ (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}).comap (algebraMap 𝒪 R) := by
    intro n
    rw [Ideal.span_le]
    rintro _ ⟨rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  let a : ∀ n : ℕ, (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* modPow π R n := fun n =>
    Ideal.quotientMap (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (algebraMap 𝒪 R) (hcomap n)
  have ha : ∀ n : ℕ, (a n).comp (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) = algebraMap 𝒪 (modPow π R n) := by
    intro n
    ext o
    show Ideal.quotientMap _ (algebraMap 𝒪 R) (hcomap n) (Ideal.Quotient.mk _ o) = _
    rw [Ideal.quotientMap_mk, IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n), Ideal.Quotient.algebraMap_eq]
  let b : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) := fun n =>
    Spec.map (CommRingCat.ofHom (a n))
  have hb : ∀ n : ℕ, b n ≫ sR n = Scheme.specOver (modPow π R n) := by
    intro n
    simp only [b, sR, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ha]

  have htrans_alg : ∀ n : ℕ, (modPowTransition π R n).toRingHom.comp (algebraMap R (modPow π R (n + 1))) = algebraMap R (modPow π R n) := by
    intro n; ext x; rfl
  have htrans_a : ∀ n : ℕ, (modPowTransition π R n).toRingHom.comp (a (n + 1)) = (a n).comp (Ideal.Quotient.factor (hle n)) := by
    intro n
    apply Ideal.Quotient.ringHom_ext
    ext o
    rfl

  haveI hmono : ∀ n : ℕ, Mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) := fun n => by
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance

  let qpt : AdicPoint K₀ π R → ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ D.Y n := fun x n =>
    D.q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)
  have hqpt_theta : ∀ (x : AdicPoint K₀ π R) (n : ℕ),
      qpt x n ≫ v n ≫ Limits.pullback.fst f (sR n) =
        (Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1 :=
    fun x n => hv_q n (modPow π R n) (hmod n) _
  have hqpt_snd : ∀ (x : AdicPoint K₀ π R) (n : ℕ),
      qpt x n ≫ v n ≫ Limits.pullback.snd f (sR n) = b n := by
    intro x n
    rw [hv_over]
    apply (cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))).1
    rw [Category.assoc, D.q_over]
    exact (hb n).symm
  refine ⟨fun p => ?_, fun x x' => ?_⟩
  ·
    let pn : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ 𝒳 := fun n =>
      Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ p.1
    have hpn : ∀ n : ℕ, pn n ≫ f = b n ≫ sR n := by
      intro n
      simp only [pn, Category.assoc, p.2, hb, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    let lf : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ Limits.pullback f (sR n) := fun n =>
      Limits.pullback.lift (pn n) (b n) (hpn n)
    let η : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ D.Y n := fun n => lf n ≫ inv (v n)
    have hη₁ : ∀ n : ℕ, η n ≫ D.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n))) := by
      intro n
      simp only [η, Category.assoc]
      rw [← hv_over n, Category.assoc, IsIso.inv_hom_id_assoc, ← Category.assoc, Limits.pullback.lift_snd]
      exact hb n
    have hη₂ : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ η (n + 1) = η n ≫ D.yt n := by
      intro n
      apply (cancel_mono (v (n + 1))).1
      simp only [η, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [(hv_sq n).w, IsIso.inv_hom_id_assoc]
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc, Limits.pullback.lift_fst, hxn₁]
        simp only [lf, Limits.pullback.lift_fst, pn, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, htrans_alg]
      · simp only [Category.assoc, Limits.pullback.lift_snd, hxn₂]
        simp only [lf, Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd, b, tR, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, htrans_a]
    obtain ⟨x, hx⟩ := hsurjD η hη₁ hη₂
    refine ⟨x, fun n => ?_⟩
    rw [← hqpt_theta x n]
    show pn n = _
    have : qpt x n = η n := (hx n).symm
    rw [this]
    simp only [η, lf, Category.assoc, IsIso.inv_hom_id_assoc, Limits.pullback.lift_fst]
  ·
    rw [← hfibD x x']
    refine forall_congr' fun n => ?_
    constructor
    · intro h
      have h1 := congrArg Subtype.val h
      rw [← hqpt_theta x n, ← hqpt_theta x' n] at h1
      apply (cancel_mono (v n)).1
      apply Limits.pullback.hom_ext
      · simpa only [Category.assoc] using h1
      · rw [Category.assoc, Category.assoc, hqpt_snd, hqpt_snd]
    · intro h
      apply Subtype.ext
      exact (hqpt_theta x n).symm.trans ((congrArg (fun t => t ≫ v n ≫ Limits.pullback.fst f (sR n)) h).trans (hqpt_theta x' n))

end S_CerednikDrinfeld_forall_exists_adicPoint_and_theta_eq_iff_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_forall_exists_adicPoint_and_theta_eq_iff_of_cerednikDrinfeld_quotient (solution)
