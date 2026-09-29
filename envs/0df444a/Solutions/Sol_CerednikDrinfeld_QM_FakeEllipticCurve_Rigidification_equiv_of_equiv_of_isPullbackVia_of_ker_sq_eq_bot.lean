-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5eeac96e-ba10-591f-bbd3-646f70f9e9a6

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsIsogenyPair_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace H2Aux

open CerednikDrinfeld.QM

theorem specMap_ofHom_id (S : Type) [CommRing S] :
    Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 (Spec (CommRingCat.of S)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (e : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst e
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem exists_comparison {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S' S : Type} [CommRing S'] [CommRing S] (φ : S' →+* S)
    (E : FakeEllipticCurve Λ N S')
    (E₁ : FakeEllipticCurve Λ N S) (g₁ : E₁.A ⟶ E.A) (h₁ : FakeEllipticCurve.IsPullbackVia φ E E₁ g₁)
    (E₂ : FakeEllipticCurve Λ N S) (g₂ : E₂.A ⟶ E.A) (h₂ : FakeEllipticCurve.IsPullbackVia φ E E₂ g₂) :
    ∃ h : E₂.A ⟶ E₁.A, h ≫ g₁ = g₂ ∧ h ≫ E₁.f = E₂.f ∧ FakeEllipticCurve.IsPullbackVia (RingHom.id S) E₁ E₂ h := by
  obtain ⟨sq₁, hmul₁, hact₁, hlev₁⟩ := h₁
  obtain ⟨sq₂, hmul₂, hact₂, hlev₂⟩ := h₂
  have hid := specMap_ofHom_id S
  let h : E₂.A ⟶ E₁.A := sq₁.lift g₂ E₂.f sq₂.w
  have hg : h ≫ g₁ = g₂ := sq₁.lift_fst _ _ _
  have hf : h ≫ E₁.f = E₂.f := sq₁.lift_snd _ _ _
  have sqh : IsPullback h E₂.f E₁.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    have s : IsPullback (h ≫ g₁) E₂.f E.f
        (Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ Spec.map (CommRingCat.ofHom φ)) := by
      rw [hg, hid, Category.id_comp]; exact sq₂
    exact IsPullback.of_right s (by rw [hf, hid, Category.comp_id]) sq₁
  refine ⟨h, hg, hf, sqh, ?_, ?_, ?_⟩
  · intro T t' P Q
    apply sq₁.hom_ext
    · rw [Category.assoc, hg, hmul₂ t' P Q, hmul₁]
      refine mul_val_congr E.L (by rw [hid, Category.comp_id]) _ _ _ _ ?_ ?_
      · show P.1 ≫ g₂ = (P.1 ≫ h) ≫ g₁
        rw [Category.assoc, hg]
      · show Q.1 ≫ g₂ = (Q.1 ≫ h) ≫ g₁
        rw [Category.assoc, hg]
    · rw [Category.assoc, hf, (E₂.L.mul t' P Q).2, (E₁.L.mul _ _ _).2, hid, Category.comp_id]
  · intro x
    apply sq₁.hom_ext
    · rw [Category.assoc, hg, hact₂, Category.assoc, hact₁, ← Category.assoc, hg]
    · rw [Category.assoc, hf, E₂.act_over, Category.assoc, E₁.act_over, hf]
  · intro T t' P hP
    have hP' := hlev₂ t' P hP
    exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
      E φ E₁ g₁ ⟨sq₁, hmul₁, hact₁, hlev₁⟩ t' ⟨P.1 ≫ h, by rw [Category.assoc, hf]; exact P.2⟩
      (by obtain ⟨P₀, hP₀⟩ := hP'; exact ⟨P₀, by rw [hP₀, Category.assoc, hg]⟩)

theorem isIsogenyPair_one {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S' S : Type} [CommRing S'] [CommRing S] (φ : S' →+* S)
    (E : FakeEllipticCurve Λ N S')
    (E₁ : FakeEllipticCurve Λ N S) (g₁ : E₁.A ⟶ E.A) (h₁ : FakeEllipticCurve.IsPullbackVia φ E E₁ g₁)
    (E₂ : FakeEllipticCurve Λ N S) (g₂ : E₂.A ⟶ E.A) (h₂ : FakeEllipticCurve.IsPullbackVia φ E E₂ g₂)
    (u : E₂.A ⟶ E₁.A) (hug : u ≫ g₁ = g₂) (huf : u ≫ E₁.f = E₂.f)
    (hu : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E₁ E₂ u)
    (v : E₁.A ⟶ E₂.A) (hvg : v ≫ g₂ = g₁) (hvf : v ≫ E₂.f = E₁.f)
    (hv : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E₂ E₁ v) :
    FakeEllipticCurve.IsIsogenyPair 1 E₂ E₁ u v := by
  obtain ⟨sq₁, -, -, -⟩ := h₁
  obtain ⟨sq₂, -, -, -⟩ := h₂
  obtain ⟨squ, hmulu, hactu, -⟩ := hu
  obtain ⟨sqv, hmulv, hactv, -⟩ := hv
  have hid := specMap_ofHom_id S
  have huv : u ≫ v = 𝟙 _ := by
    apply sq₂.hom_ext
    · rw [Category.assoc, hvg, hug, Category.id_comp]
    · rw [Category.assoc, hvf, huf, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply sq₁.hom_ext
    · rw [Category.assoc, hug, hvg, Category.id_comp]
    · rw [Category.assoc, huf, hvf, Category.id_comp]
  refine ⟨huf, hvf, ?_, ?_, hactu, hactv, ?_⟩
  · intro T t P Q
    apply Subtype.ext
    show (E₂.L.mul t P Q).1 ≫ u = (E₁.L.mul t (mapPt u huf P) (mapPt u huf Q)).1
    rw [hmulu t P Q]
    exact mul_val_congr E₁.L (by rw [hid, Category.comp_id]) _ _ _ _ rfl rfl
  · intro T t P Q
    apply Subtype.ext
    show (E₁.L.mul t P Q).1 ≫ v = (E₂.L.mul t (mapPt v hvf P) (mapPt v hvf Q)).1
    rw [hmulv t P Q]
    exact mul_val_congr E₂.L (by rw [hid, Category.comp_id]) _ _ _ _ rfl rfl
  · intro hd
    have e1 : (((1 : ℕ) : ℚ) : ℍ[ℚ, a, b]) = 1 := by simp
    have hmem : (1 : ℍ[ℚ, a, b]) ∈ Λ := by rw [← e1]; exact hd
    have hsub : (⟨(((1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ : ↥Λ) = ⟨1, hmem⟩ := Subtype.ext e1
    refine ⟨?_, ?_⟩
    · rw [huv, hsub, E₂.act_one]
    · rw [hvu, hsub, E₁.act_one]

end H2Aux

theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (B B₀ : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀) (hp : Function.Surjective p) (hp2 : RingHom.ker (p : B →+* B₀) ^ 2 = ⊥)
    (ψ : Onr →ₐ[𝒪] B)

    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ρ₀ ρ₀' : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀)
    (h : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ρ ρ₀)
    (h' : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ρ' ρ₀')
    (he : FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ₀ ρ₀') :
    FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ ρ' := by
  classical

  obtain ⟨ub, uAh, hub, hubg, huAh, huAhg, -, hφ⟩ := h
  obtain ⟨ub', uAh', hub', hubg', huAh', huAhg', -, hφ'⟩ := h'
  have hub'c := hub'
  obtain ⟨u₀, uA₀, ⟨hu₀, hu₀g, huA₀, huA₀g⟩, i, j, hij⟩ := he

  obtain ⟨u, hug, huf, hu⟩ := H2Aux.exists_comparison _ E ρ.Eb ρ.gb ρ.isPullback_Eb ρ'.Eb ρ'.gb ρ'.isPullback_Eb
  obtain ⟨uA, huAg, huAf, huA⟩ := H2Aux.exists_comparison _ A₀ ρ.Ab ρ.gA ρ.isPullback_Ab ρ'.Ab ρ'.gA ρ'.isPullback_Ab
  refine ⟨u, uA, ⟨hu, hug, huA, huAg⟩, i, j, ?_⟩

  obtain ⟨u', hu'g, hu'f, hu'⟩ := H2Aux.exists_comparison _ E ρ'.Eb ρ'.gb ρ'.isPullback_Eb ρ.Eb ρ.gb ρ.isPullback_Eb
  obtain ⟨uA', huA'g, huA'f, huA'⟩ := H2Aux.exists_comparison _ A₀ ρ'.Ab ρ'.gA ρ'.isPullback_Ab ρ.Ab ρ.gA ρ.isPullback_Ab
  have pu : FakeEllipticCurve.IsIsogenyPair 1 ρ'.Eb ρ.Eb u u' :=
    H2Aux.isIsogenyPair_one _ E ρ.Eb ρ.gb ρ.isPullback_Eb ρ'.Eb ρ'.gb ρ'.isPullback_Eb u hug huf hu u' hu'g hu'f hu'
  have puA : FakeEllipticCurve.IsIsogenyPair 1 ρ'.Ab ρ.Ab uA uA' :=
    H2Aux.isIsogenyPair_one _ A₀ ρ.Ab ρ.gA ρ.isPullback_Ab ρ'.Ab ρ'.gA ρ'.isPullback_Ab uA huAg huAf huA uA' huA'g huA'f huA'
  have pair1 : FakeEllipticCurve.IsIsogenyPair (r ^ ρ.d) ρ'.Eb ρ.Ab (u ≫ ρ.φ) (ρ.φ' ≫ u') := by
    have h := CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair.comp hΛℤ pu ρ.isIsogenyPair
    rwa [one_mul] at h
  have pair2 : FakeEllipticCurve.IsIsogenyPair (r ^ ρ'.d) ρ'.Eb ρ.Ab (ρ'.φ ≫ uA) (uA' ≫ ρ'.φ') := by
    have h := CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair.comp hΛℤ ρ'.isIsogenyPair puA
    rwa [mul_one] at h

  have hnil : ∀ (hle : Ideal.span {algebraMap 𝒪 B π} ≤ (Ideal.span {algebraMap 𝒪 B₀ π}).comap (p : B →+* B₀)),
      ∃ n : ℕ, RingHom.ker (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀) hle) ^ n = ⊥ := by
    intro hle
    refine ⟨2, ?_⟩
    have hsub : RingHom.ker (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀) hle) ≤
        (RingHom.ker (p : B →+* B₀)).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
      obtain ⟨c₀, hc₀⟩ := hx
      obtain ⟨c, rfl⟩ := hp c₀
      have hπ : algebraMap 𝒪 B₀ π = p (algebraMap 𝒪 B π) := (p.commutes π).symm
      have hmem : y - c * algebraMap 𝒪 B π ∈ RingHom.ker (p : B →+* B₀) := by
        rw [RingHom.mem_ker, map_sub, map_mul]
        show p y - p c * p (algebraMap 𝒪 B π) = 0
        rw [← hπ, hc₀]
        exact sub_self (p y)
      have hy : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}) y =
          Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}) (y - c * algebraMap 𝒪 B π) := by
        rw [Ideal.Quotient.eq, sub_sub_cancel]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      rw [hy]
      exact Ideal.mem_map_of_mem _ hmem
    rw [eq_bot_iff]
    calc RingHom.ker (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀) hle) ^ 2
        ≤ ((RingHom.ker (p : B →+* B₀)).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) ^ 2 :=
          Ideal.pow_right_mono hsub 2
      _ = ((RingHom.ker (p : B →+* B₀)) ^ 2).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) :=
          (Ideal.map_pow _ _ 2).symm
      _ = ⊥ := by rw [hp2, Ideal.map_bot]
      _ ≤ ⊥ := le_rfl

  obtain ⟨sqρ, -, -, -⟩ := ρ.isPullback_Eb
  obtain ⟨sqρA, -, -, -⟩ := ρ.isPullback_Ab
  obtain ⟨sqb, -, -, -⟩ := hub
  obtain ⟨sq', -, -, -⟩ := hub'c
  obtain ⟨sq₀, -, -, -⟩ := hu₀
  obtain ⟨sqA, -, hactA, -⟩ := huAh
  obtain ⟨sqA', -, -, -⟩ := huAh'
  obtain ⟨sqA₀, -, -, -⟩ := huA₀
  have hid₀ := H2Aux.specMap_ofHom_id (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π})
  have hidB := H2Aux.specMap_ofHom_id (B ⧸ Ideal.span {algebraMap 𝒪 B π})

  have hA : ub' ≫ u = u₀ ≫ ub := by
    apply sqρ.hom_ext
    · rw [Category.assoc, hug, hubg', Category.assoc, hubg, ← Category.assoc, hu₀g]
    · rw [Category.assoc, huf, sq'.w, Category.assoc, sqb.w, ← Category.assoc, sq₀.w, hid₀, Category.comp_id]

  have hB : uAh' ≫ uA = uA₀ ≫ uAh := by
    apply sqρA.hom_ext
    · rw [Category.assoc, huAg, huAhg', Category.assoc, huAhg, huA₀g]
    · rw [Category.assoc, huAf, sqA'.w, Category.assoc, sqA.w, ← Category.assoc, sqA₀.w, hid₀, Category.comp_id]
  have hcalc : ub' ≫ u ≫ ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ub' ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    calc ub' ≫ u ≫ ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩
        = u₀ ≫ (ub ≫ ρ.φ) ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          rw [← Category.assoc, hA]; simp only [Category.assoc]
      _ = u₀ ≫ ρ₀.φ ≫ (uAh ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by rw [hφ]; simp only [Category.assoc]
      _ = (u₀ ≫ ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uAh := by rw [← hactA]; simp only [Category.assoc]
      _ = (ρ₀'.φ ≫ uA₀ ≫ ρ₀.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uAh := by rw [hij]
      _ = ρ₀'.φ ≫ uA₀ ≫ uAh ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [← hactA]; simp only [Category.assoc]
      _ = ρ₀'.φ ≫ (uAh' ≫ uA) ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hB]; simp only [Category.assoc]
      _ = (ub' ≫ ρ'.φ) ≫ uA ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hφ']; simp only [Category.assoc]
      _ = ub' ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]

  have hagree : ub' ≫ (u ≫ ρ.φ) ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ub' ≫ (ρ'.φ ≫ uA) ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    simpa only [Category.assoc] using hcalc
  have H := CerednikDrinfeld.QM.FakeEllipticCurve.comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
    hΛℤ r _ _ _ (Ideal.quotientMap_surjective hp) (hnil _) ρ'.Eb ρ₀'.Eb ρ.Ab ub' hub' ρ.d ρ'.d
    (u ≫ ρ.φ) (ρ'.φ ≫ uA) (ρ.φ' ≫ u') (uA' ≫ ρ'.φ') pair1 pair2 i j hagree
  simpa only [Category.assoc] using H

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot (solution)
