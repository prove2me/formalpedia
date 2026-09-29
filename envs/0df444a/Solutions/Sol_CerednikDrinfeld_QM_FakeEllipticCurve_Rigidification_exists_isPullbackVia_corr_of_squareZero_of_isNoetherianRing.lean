-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/67e13d49-c107-503a-90a9-6874a9e82a61

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_comp_eq_comp_of_preservesLevel_of_isNilpotent_ker_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace DRLasm

universe u

variable {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}

theorem mapPt_mapPt (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    (h : (φ ≫ ψ) ≫ f'' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

variable (L : GoodReductionJacobian.RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem act_comm_natCast {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (x : ↥Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act x ≫ E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ ≫ E.act x := by
  have hnx : ((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [QuaternionAlgebra.coe_natCast, ← nsmul_eq_mul]; exact nsmul_mem x.2 n
  have hxn : (x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [QuaternionAlgebra.coe_natCast, ← nsmul_eq_mul']; exact nsmul_mem x.2 n
  have h1 := E.act_mul ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ x hnx
  have h2 := E.act_mul x ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ hxn
  have h3 : (⟨((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hnx⟩ : ↥Λ) = ⟨(x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]), hxn⟩ :=
    Subtype.ext (QuaternionAlgebra.coe_commutes _ _)
  rw [← h1, h3, h2]

end DRLasm

open DRLasm in
theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀) (hp : Function.Surjective p) (hp2 : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (ψ : Onr →ₐ[𝒪] B) (hNb : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))

    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g)
    (ρ₀ : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀) :
    ∃ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀)
      (_ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ρ ρ'),
      ∃ (ib : ρ₀.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ₀.gb ≫ (Iso.refl E₀.A).hom) (_ : ib ≫ ρ'.Eb.f = ρ₀.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ'.Ab uA) (_ : uA ≫ ρ₀.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  obtain ⟨hsqg, gmul, gact, glev⟩ := hg
  obtain ⟨hsq0b, b0mul, b0act, b0lev⟩ := ρ₀.isPullback_Eb
  obtain ⟨hsq0A, A0mul, A0act, A0lev⟩ := ρ₀.isPullback_Ab
  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := ρ₀.isIsogenyPair

  have hnat : ∀ n : ℕ, (((n : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun n => by exact_mod_cast hΛℤ n
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ 1

  let pb : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π}) :=
    Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
            exact Ideal.subset_span rfl))))
  have hpb : pb.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (p : B →+* B₀) := Ideal.quotientMap_comp_mk _
  let ψb := FakeEllipticCurve.Rigidification.residueLeg π ψ
  have hres : FakeEllipticCurve.Rigidification.residueLeg π (p.comp ψ) = pb.comp ψb := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp [FakeEllipticCurve.Rigidification.residueLeg, Ideal.quotientMap_mk, pb, ψb]
  have hSpecE : Spec.map (CommRingCat.ofHom pb) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B₀ π}))) ≫ Spec.map (CommRingCat.ofHom (p : B →+* B₀)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hpb]
  have hSpecA : Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π (p.comp ψ))) =
      Spec.map (CommRingCat.ofHom pb) ≫ Spec.map (CommRingCat.ofHom ψb) := by
    rw [hres, CommRingCat.ofHom_comp, Spec.map_comp]

  have hpb_surj : Function.Surjective pb := Ideal.quotientMap_surjective hp
  have hlift : ∀ x : B, pb (Ideal.Quotient.mk _ x) = 0 → ∃ x' c : B, p x' = 0 ∧ x = x' + c * algebraMap 𝒪 B π := by
    intro x hx
    have hx' : (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B₀ π})) (p x) = 0 := by
      simpa [pb, Ideal.quotientMap_mk] using hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx'
    obtain ⟨c₀, hc₀⟩ := hx'
    obtain ⟨c, rfl⟩ := hp c₀
    refine ⟨x - c * algebraMap 𝒪 B π, c, ?_, by ring⟩
    rw [map_sub, map_mul, p.commutes π, ← hc₀, sub_self]
  have hpb2 : ∀ s t : B ⧸ Ideal.span {algebraMap 𝒪 B π}, pb s = 0 → pb t = 0 → s * t = 0 := by
    intro s t hs ht
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨x', c, hx', rfl⟩ := hlift x hs
    obtain ⟨y', d, hy', rfl⟩ := hlift y ht
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have hxy : (x' + c * algebraMap 𝒪 B π) * (y' + d * algebraMap 𝒪 B π)
        = x' * y' + (x' * d + c * y' + c * d * algebraMap 𝒪 B π) * algebraMap 𝒪 B π := by ring
    rw [hxy, hp2 x' y' hx' hy', zero_add]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hI : IsNilpotent (RingHom.ker pb) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_bot]
    exact hpb2 x y hx hy
  have hr : IsNilpotent ((r : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}) := by
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hmem : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    have hcast : ((r : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}) =
        Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}) (algebraMap 𝒪 B ((r : ℕ) : 𝒪)) := by
      rw [map_natCast, map_natCast]
    rw [hcast, Ideal.Quotient.eq_zero_iff_mem, ← hc, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

  obtain ⟨Eb, gE, hsqE, Emul, Eact, Elev, Elev'⟩ :=
    FakeEllipticCurve.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E
  obtain ⟨Ab, gA0, hsqA, Amul, Aact, Alev, Alev'⟩ := FakeEllipticCurve.exists_isPullback_levelIff ψb A₀

  have wub : (ρ₀.gb ≫ g) ≫ E.f = (ρ₀.Eb.f ≫ Spec.map (CommRingCat.ofHom pb)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) := by
    rw [Category.assoc, hsqg.w, ← Category.assoc, hsq0b.w, Category.assoc, ← hSpecE, Category.assoc]
  let ub : ρ₀.Eb.A ⟶ Eb.A := hsqE.lift (ρ₀.gb ≫ g) _ wub
  have hub₁ : ub ≫ gE = ρ₀.gb ≫ g := hsqE.lift_fst _ _ _
  have hub₂ : ub ≫ Eb.f = ρ₀.Eb.f ≫ Spec.map (CommRingCat.ofHom pb) := hsqE.lift_snd _ _ _
  have hsq_ub : IsPullback ub ρ₀.Eb.f Eb.f (Spec.map (CommRingCat.ofHom pb)) := by
    have big := hsq0b.paste_horiz hsqg
    rw [← hub₁, ← hSpecE] at big
    exact big.of_right hub₂ hsqE
  have wuA : ρ₀.gA ≫ A₀.f = (ρ₀.Ab.f ≫ Spec.map (CommRingCat.ofHom pb)) ≫ Spec.map (CommRingCat.ofHom ψb) := by
    rw [hsq0A.w, hSpecA, Category.assoc]
  let uA : ρ₀.Ab.A ⟶ Ab.A := hsqA.lift ρ₀.gA _ wuA
  have huA₁ : uA ≫ gA0 = ρ₀.gA := hsqA.lift_fst _ _ _
  have huA₂ : uA ≫ Ab.f = ρ₀.Ab.f ≫ Spec.map (CommRingCat.ofHom pb) := hsqA.lift_snd _ _ _
  have hsq_uA : IsPullback uA ρ₀.Ab.f Ab.f (Spec.map (CommRingCat.ofHom pb)) := by
    have big := hsq0A
    rw [← huA₁, hSpecA] at big
    exact big.of_right huA₂ hsqA
  have hubV : FakeEllipticCurve.IsPullbackVia pb Eb ρ₀.Eb ub := by
    refine ⟨hsq_ub, ?_, ?_, ?_⟩
    · intro T t' P Q
      apply hsqE.hom_ext
      · rw [Category.assoc, hub₁, ← Category.assoc, b0mul, gmul, Emul]
        exact mul_val_congr E.L (by simp only [Category.assoc, hSpecE]) _ _ _ _
          (by simp only [Category.assoc, hub₁]) (by simp only [Category.assoc, hub₁])
      · rw [Category.assoc, hub₂, ← Category.assoc, (ρ₀.Eb.L.mul t' P Q).2, (Eb.L.mul _ _ _).2]
    · intro x
      apply hsqE.hom_ext
      · have e1 : (ρ₀.Eb.act x ≫ ub) ≫ gE = ρ₀.gb ≫ g ≫ E.act x := by
          rw [Category.assoc, hub₁, ← Category.assoc, b0act, Category.assoc, gact]
        have e2 : (ub ≫ Eb.act x) ≫ gE = ρ₀.gb ≫ g ≫ E.act x := by
          rw [Category.assoc, Eact, ← Category.assoc, hub₁, Category.assoc]
        exact e1.trans e2.symm
      · rw [Category.assoc, hub₂, ← Category.assoc, ρ₀.Eb.act_over, Category.assoc, Eb.act_over, hub₂]
    · intro T t' P hP
      obtain ⟨P₁, hP₁⟩ := b0lev t' P hP
      obtain ⟨P₂, hP₂⟩ := glev (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B₀ π}))))
        ⟨P.1 ≫ ρ₀.gb, by rw [Category.assoc, hsq0b.w, ← Category.assoc, P.2]⟩ ⟨P₁, hP₁⟩
      exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
        (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E Eb gE hsqE Emul Elev
        (t' ≫ Spec.map (CommRingCat.ofHom pb))
        ⟨P.1 ≫ ub, by rw [Category.assoc, hsq_ub.w, ← Category.assoc, P.2]⟩
        ⟨P₂, by rw [hP₂]; simp only [Category.assoc, hub₁]⟩
  have huAV : FakeEllipticCurve.IsPullbackVia pb Ab ρ₀.Ab uA := by
    refine ⟨hsq_uA, ?_, ?_, ?_⟩
    · intro T t' P Q
      apply hsqA.hom_ext
      · rw [Category.assoc, huA₁, A0mul, Amul]
        exact mul_val_congr A₀.L (by rw [hSpecA, Category.assoc]) _ _ _ _
          (by simp only [Category.assoc, huA₁]) (by simp only [Category.assoc, huA₁])
      · rw [Category.assoc, huA₂, ← Category.assoc, (ρ₀.Ab.L.mul t' P Q).2, (Ab.L.mul _ _ _).2]
    · intro x
      apply hsqA.hom_ext
      · have e1 : (ρ₀.Ab.act x ≫ uA) ≫ gA0 = ρ₀.gA ≫ A₀.act x := by
          rw [Category.assoc, huA₁, A0act]
        have e2 : (uA ≫ Ab.act x) ≫ gA0 = ρ₀.gA ≫ A₀.act x := by
          rw [Category.assoc, Aact, ← Category.assoc, huA₁]
        exact e1.trans e2.symm
      · rw [Category.assoc, huA₂, ← Category.assoc, ρ₀.Ab.act_over, Category.assoc, Ab.act_over, huA₂]
    · intro T t' P hP
      obtain ⟨P₁, hP₁⟩ := A0lev t' P hP
      exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
        ψb A₀ Ab gA0 hsqA Amul Alev (t' ≫ Spec.map (CommRingCat.ofHom pb))
        ⟨P.1 ≫ uA, by rw [Category.assoc, hsq_uA.w, ← Category.assoc, P.2]⟩
        ⟨P₁, by rw [hP₁, Category.assoc, huA₁]⟩

  obtain ⟨m, φ, hφ, φ_mul, φ_act, hred⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
      coord hcoord pb hpb_surj hpb2 hr Eb Ab ρ₀.Eb ρ₀.Ab ub hubV uA huAV ρ₀.φ ρ₀.φ_over hφmul hφlin
  obtain ⟨m', φ', hφ', φ'_mul, φ'_act, hred'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
      coord hcoord pb hpb_surj hpb2 hr Ab Eb ρ₀.Ab ρ₀.Eb uA huAV ub hubV ρ₀.φ' hφ'o hφ'mul hφ'lin

  have hpair : FakeEllipticCurve.IsIsogenyPair (r ^ (ρ₀.d + m + m')) Eb Ab φ φ' :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
      hΛℤ pb hpb_surj hI Eb Ab ρ₀.Eb ρ₀.Ab ub hubV uA huAV φ hφ φ' hφ' φ_mul φ'_mul φ_act φ'_act
      ρ₀.φ ρ₀.φ_over ρ₀.φ' hφ'o ρ₀.d m m' ρ₀.isIsogenyPair hred hred'

  let cm : ↥Λ := ⟨(((r ^ m : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat (r ^ m)⟩
  let cm' : ↥Λ := ⟨(((r ^ m' : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat (r ^ m')⟩
  let φ₁ : ρ₀.Eb.A ⟶ ρ₀.Ab.A := ρ₀.φ ≫ ρ₀.Ab.act cm
  let φ₁' : ρ₀.Ab.A ⟶ ρ₀.Eb.A := ρ₀.φ' ≫ ρ₀.Eb.act cm'
  have hφ₁ : φ₁ ≫ ρ₀.Ab.f = ρ₀.Eb.f := by
    simp only [φ₁, Category.assoc, ρ₀.Ab.act_over]; exact ρ₀.φ_over
  have hφ₁' : φ₁' ≫ ρ₀.Eb.f = ρ₀.Ab.f := by
    simp only [φ₁', Category.assoc, ρ₀.Eb.act_over]; exact hφ'o
  have key : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π}))}
      (P : SchemeHomOver t ρ₀.Eb.f), mapPt φ₁ hφ₁ P = pushPt (ρ₀.Ab.act cm) (ρ₀.Ab.act_over cm) (mapPt ρ₀.φ ρ₀.φ_over P) :=
    fun P => Subtype.ext (by simp only [mapPt_coe, φ₁, Category.assoc])
  have key' : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π}))}
      (P : SchemeHomOver t ρ₀.Ab.f), mapPt φ₁' hφ₁' P = pushPt (ρ₀.Eb.act cm') (ρ₀.Eb.act_over cm') (mapPt ρ₀.φ' hφ'o P) :=
    fun P => Subtype.ext (by simp only [mapPt_coe, φ₁', Category.assoc])
  have φ₁_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π})))
      (P Q : SchemeHomOver t ρ₀.Eb.f),
      mapPt φ₁ hφ₁ (ρ₀.Eb.L.mul t P Q) = ρ₀.Ab.L.mul t (mapPt φ₁ hφ₁ P) (mapPt φ₁ hφ₁ Q) := by
    intro T t P Q
    rw [key, key, key, hφmul, ρ₀.Ab.act_hom]
  have φ₁'_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π})))
      (P Q : SchemeHomOver t ρ₀.Ab.f),
      mapPt φ₁' hφ₁' (ρ₀.Ab.L.mul t P Q) = ρ₀.Eb.L.mul t (mapPt φ₁' hφ₁' P) (mapPt φ₁' hφ₁' Q) := by
    intro T t P Q
    rw [key', key', key', hφ'mul, ρ₀.Eb.act_hom]
  have φ₁_act : ∀ x : ↥Λ, ρ₀.Eb.act x ≫ φ₁ = φ₁ ≫ ρ₀.Ab.act x := by
    intro x
    simp only [φ₁]
    rw [← Category.assoc, hφlin x, Category.assoc, Category.assoc, act_comm_natCast]
  have φ₁'_act : ∀ x : ↥Λ, ρ₀.Ab.act x ≫ φ₁' = φ₁' ≫ ρ₀.Eb.act x := by
    intro x
    simp only [φ₁']
    rw [← Category.assoc, hφ'lin x, Category.assoc, Category.assoc, act_comm_natCast]
  have hred₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π})))
      (P : SchemeHomOver t ρ₀.Eb.f),
      P.1 ≫ 𝟙 _ ≫ φ₁ = (nsmulPt ρ₀.Ab.L t (r ^ m) (mapPt ρ₀.φ ρ₀.φ_over P)).1 ≫ 𝟙 _ := by
    intro T t P
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ₀.Ab h1 (r ^ m) (hnat _) t]
    simp only [mapPt_coe, φ₁, cm, Category.assoc, Category.id_comp, Category.comp_id]
  have hred₁' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π})))
      (Q : SchemeHomOver t ρ₀.Ab.f),
      Q.1 ≫ 𝟙 _ ≫ φ₁' = (nsmulPt ρ₀.Eb.L t (r ^ m') (mapPt ρ₀.φ' hφ'o Q)).1 ≫ 𝟙 _ := by
    intro T t Q
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ₀.Eb h1 (r ^ m') (hnat _) t]
    simp only [mapPt_coe, φ₁', cm', Category.assoc, Category.id_comp, Category.comp_id]
  have hI0 : IsNilpotent (RingHom.ker (RingHom.id (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π}))) := by
    refine ⟨1, ?_⟩
    rw [pow_one, Ideal.zero_eq_bot, eq_bot_iff]
    intro x hx
    rw [RingHom.mem_ker, RingHom.id_apply] at hx
    rw [hx]; exact Ideal.zero_mem _
  have hpair₀ : FakeEllipticCurve.IsIsogenyPair (r ^ (ρ₀.d + m + m')) ρ₀.Eb ρ₀.Ab φ₁ φ₁' :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
      hΛℤ (RingHom.id _) Function.surjective_id hI0 ρ₀.Eb ρ₀.Ab ρ₀.Eb ρ₀.Ab (𝟙 _)
      (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ρ₀.Eb) (𝟙 _)
      (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ρ₀.Ab)
      φ₁ hφ₁ φ₁' hφ₁' φ₁_mul φ₁'_mul φ₁_act φ₁'_act ρ₀.φ ρ₀.φ_over ρ₀.φ' hφ'o ρ₀.d m m' ρ₀.isIsogenyPair hred₁ hred₁'
  have h₀lev : FakeEllipticCurve.PreservesLevel ρ₀.Eb ρ₀.Ab φ₁ hφ₁ := by
    intro T t P hP
    rw [key]
    exact ρ₀.Ab.lev_stable cm t _ (ρ₀.preservesLevel t P hP)

  have hredEq : ub ≫ φ = φ₁ ≫ uA := by
    have := hred ρ₀.Eb.f ⟨𝟙 _, Category.id_comp _⟩
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ₀.Ab h1 (r ^ m) (hnat _)] at this
    simpa only [mapPt_coe, φ₁, cm, Category.assoc, Category.id_comp] using this
  have hredEq' : uA ≫ φ' = φ₁' ≫ ub := by
    have := hred' ρ₀.Ab.f ⟨𝟙 _, Category.id_comp _⟩
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ₀.Eb h1 (r ^ m') (hnat _)] at this
    simpa only [mapPt_coe, φ₁', cm', Category.assoc, Category.id_comp] using this
  have hlev : FakeEllipticCurve.PreservesLevel Eb Ab φ hφ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_comp_eq_comp_of_preservesLevel_of_isNilpotent_ker_of_isUnit
      pb hpb_surj hI hNb Eb Ab ρ₀.Eb ρ₀.Ab ub hubV uA huAV φ hφ φ_mul φ₁ hφ₁ hredEq h₀lev

  refine ⟨{ Eb := Eb, gb := gE, isPullback_Eb := ⟨hsqE, Emul, Eact, Elev⟩, Ab := Ab, gA := gA0,
            isPullback_Ab := ⟨hsqA, Amul, Aact, Alev⟩, d := ρ₀.d + m + m', φ := φ, φ' := φ', φ_over := hφ,
            isIsogenyPair := hpair, preservesLevel := hlev },
          { Eb := ρ₀.Eb, gb := ρ₀.gb, isPullback_Eb := ρ₀.isPullback_Eb, Ab := ρ₀.Ab, gA := ρ₀.gA,
            isPullback_Ab := ρ₀.isPullback_Ab, d := ρ₀.d + m + m', φ := φ₁, φ' := φ₁', φ_over := hφ₁,
            isIsogenyPair := hpair₀, preservesLevel := h₀lev },
          ⟨ub, uA, hubV, hub₁, huAV, huA₁, rfl, hredEq⟩,
          𝟙 _, ?_, ?_, 𝟙 _, CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ρ₀.Ab, ?_, 0, m, ?_⟩
  · simp
  · simp
  · simp
  · have e0 : (⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨1, h1⟩ := Subtype.ext (by push_cast; simp)
    have em : (⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = cm := Subtype.ext (by simp only [cm]; norm_cast)
    rw [e0, em, ρ₀.Ab.act_one h1]
    simp only [φ₁, Category.id_comp, Category.comp_id, Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing (solution)
