-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3acfa2d0-bade-5585-afea-a3e84ee873d7

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_squareZero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace CorrKit

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem mul_val_congr {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}}
    {t t' : T ⟶ Spec (CommRingCat.of S)} (e : t = t') (P Q : SchemeHomOver t E.f) (P' Q' : SchemeHomOver t' E.f)
    (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) : (E.L.mul t P Q).1 = (E.L.mul t' P' Q').1 := by
  subst e
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem act_rpow_comp {S : Type} [CommRing S] (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (E : FakeEllipticCurve Λ N S) (r i j : ℕ) :
    E.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      E.act ⟨(((r ^ (i + j) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hmem : ((((r ^ j : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ i : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ j : ℕ) * (r ^ i : ℕ) : ℤ)
    push_cast at this ⊢
    exact this
  rw [← E.act_mul _ _ hmem]
  congr 1
  apply Subtype.ext
  push_cast
  rw [← pow_add, Nat.add_comm]

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

def Corr (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E) : Prop :=
  ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
    (i j : ℕ),
    ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩

theorem corr_of_corr_of_corr (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hNb : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (ρ₀ ρ₁ ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (h₁ : Corr hΛℤ ρ₀ ρ₁) (h₂ : Corr hΛℤ ρ₀ ρ₂) : Corr hΛℤ ρ₁ ρ₂ := by
  obtain ⟨ib₁, hib₁g, hib₁f, uA₁, huA₁, huA₁g, i₁, j₁, hc₁⟩ := h₁
  obtain ⟨ib₂, hib₂g, hib₂f, uA₂, huA₂, huA₂g, i₂, j₂, hc₂⟩ := h₂

  obtain ⟨v₁, hv₁g, hv₁f, hv₁⟩ :=
    FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) hNb E ρ₀.Eb ρ₀.gb ρ₀.isPullback_Eb ρ₁.Eb ρ₁.gb ρ₁.isPullback_Eb

  obtain ⟨w₁, hw₁g, hw₁f, hw₁⟩ :=
    FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hNb A₀ ρ₁.Ab ρ₁.gA ρ₁.isPullback_Ab ρ₀.Ab ρ₀.gA ρ₀.isPullback_Ab
  obtain ⟨hpb₁, -, -, -⟩ := id ρ₁.isPullback_Eb
  obtain ⟨hpbA₁, -, hactA₁, -⟩ := id ρ₁.isPullback_Ab
  obtain ⟨hw₁pb, hw₁mul, hw₁act, hw₁lev⟩ := hw₁
  obtain ⟨huA₂pb, huA₂mul, huA₂act, huA₂lev⟩ := huA₂
  have hv₁ib₁ : v₁ ≫ ib₁ = 𝟙 _ := by
    apply hpb₁.hom_ext
    · rw [Category.assoc, hib₁g, hv₁g, Category.id_comp]
    · rw [Category.assoc, hib₁f, hv₁f, Category.id_comp]
  have huA₁w₁ : uA₁ ≫ w₁ = 𝟙 _ := by
    apply hpbA₁.hom_ext
    · rw [Category.assoc, hw₁g, huA₁g, Category.id_comp]
    · rw [Category.assoc, hw₁f]
      obtain ⟨huA₁pb, -⟩ := huA₁
      have := huA₁pb.w
      simp only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] at this
      rw [this, Category.id_comp]
  refine ⟨v₁ ≫ ib₂, by rw [Category.assoc, hib₂g, hv₁g], by rw [Category.assoc, hib₂f, hv₁f],
    uA₂ ≫ w₁, ?_, by rw [Category.assoc, hw₁g, huA₂g], i₂ + j₁, i₁ + j₂, ?_⟩
  ·
    have hpb : IsPullback (uA₂ ≫ w₁) ρ₂.Ab.f ρ₁.Ab.f (Spec.map (CommRingCat.ofHom (RingHom.id _))) := by
      have e := huA₂pb.paste_horiz hw₁pb
      simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using e
    refine ⟨hpb, ?_, ?_, ?_⟩
    · intro T t' P Q
      rw [← Category.assoc, huA₂mul, hw₁mul]

      have ht : (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π})))) ≫
          Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) =
          t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) := by
        simp only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
      exact mul_val_congr ρ₁.Ab ht _ _ _ _ (by simp) (by simp)
    · intro x
      rw [← Category.assoc, huA₂act, Category.assoc, hw₁act, Category.assoc]
    · intro T t' P hP
      obtain ⟨P₁, hP₁⟩ := huA₂lev t' P hP
      obtain ⟨P₂, hP₂⟩ := hw₁lev _ ⟨P.1 ≫ uA₂, by rw [Category.assoc, huA₂pb.w, ← Category.assoc, P.2]⟩ ⟨P₁, hP₁⟩
      exact ⟨P₂, by rw [hP₂]; simp only [Category.assoc]⟩
  ·
    have e₂ := congrArg (· ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) hc₂
    have e₁ := congrArg (· ≫ ρ₀.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) hc₁
    simp only [Category.assoc] at e₁ e₂
    rw [act_rpow_comp hΛℤ, act_rpow_comp hΛℤ] at e₁ e₂
    rw [Nat.add_comm j₁ j₂] at e₁

    have e₃ : v₁ ≫ ib₂ ≫ ρ₂.φ ≫ uA₂ ≫ ρ₀.Ab.act ⟨(((r ^ (i₂ + j₁) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        ρ₁.φ ≫ uA₁ ≫ ρ₀.Ab.act ⟨(((r ^ (i₁ + j₂) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
      rw [e₂, ← e₁, ← Category.assoc v₁ ib₁, hv₁ib₁, Category.id_comp]
    have e₄ := congrArg (· ≫ w₁) e₃
    simp only [Category.assoc] at e₄
    rw [hw₁act, hw₁act, ← Category.assoc uA₁ w₁, huA₁w₁, Category.id_comp] at e₄
    simpa only [Category.assoc] using e₄

theorem equiv_of_corr (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hNb : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E) (h : Corr hΛℤ ρ ρ') :
    FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ ρ' := by
  obtain ⟨ib, hibg, hibf, uA, huA, huAg, i, j, hc⟩ := h
  obtain ⟨u, hug, huf, hu⟩ :=
    FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) hNb E ρ.Eb ρ.gb ρ.isPullback_Eb ρ'.Eb ρ'.gb ρ'.isPullback_Eb
  obtain ⟨hpb', -, -, -⟩ := id ρ'.isPullback_Eb
  have huib : u ≫ ib = 𝟙 _ := by
    apply hpb'.hom_ext
    · rw [Category.assoc, hibg, hug, Category.id_comp]
    · rw [Category.assoc, hibf, huf, Category.id_comp]
  refine ⟨u, uA, ⟨hu, hug, huA, huAg⟩, j, i, ?_⟩
  rw [← hc, ← Category.assoc u ib, huib, Category.id_comp]

theorem equiv_of_corr_of_corr (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hNb : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (ρ₀ ρ₁ ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (h₁ : Corr hΛℤ ρ₀ ρ₁) (h₂ : Corr hΛℤ ρ₀ ρ₂) : FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ₁ ρ₂ :=
  equiv_of_corr hΛℤ hNb ρ₁ ρ₂ (corr_of_corr_of_corr hΛℤ hNb ρ₀ ρ₁ ρ₂ h₁ h₂)

end CorrKit

namespace ClassLiftEX

theorem isUnit_natCast_of_isNilpotent_of_coprime {R : Type} [CommRing R] {r k : ℕ}
    (hr : IsNilpotent ((r : ℕ) : R)) (hk : Nat.Coprime k r) : IsUnit ((k : ℕ) : R) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hk
  have h1 : ((u : ℤ) : R) * (k : R) = 1 - (v : R) * (r : R) := by
    have := congrArg (Int.cast : ℤ → R) huv
    push_cast at this
    linear_combination this
  have h2 : IsUnit (1 - ((v : ℤ) : R) * (r : R)) :=
    (Commute.isNilpotent_mul_left (Commute.all _ _) hr).isUnit_one_sub
  rw [← h1] at h2
  exact isUnit_of_mul_isUnit_right h2
end ClassLiftEX

theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (S S₀ : Type) [CommRing S] [IsNoetherianRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [IsNoetherianRing S₀] [Algebra C S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
    (p : S →ₐ[C] S₀) (hp : Function.Surjective p) (hp2 : RingHom.ker (p : S →+* S₀) ^ 2 = ⊥)
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u₀ : FakeEllipticCurve.WithFullLevel Λ N n S₀)
    (g : u₀.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (p : S →+* S₀) u.1 u₀.1 g)
    (hgP : (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (p : S →+* S₀)) ≫ (u.2.P).1)
    (ρ₀ : FakeEllipticCurve.Rigidification r π A₀ ((p.restrictScalars 𝒪).comp ψS) u₀.1) :

    (∃ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ₀' : FakeEllipticCurve.Rigidification r π A₀ ((p.restrictScalars 𝒪).comp ψS) u₀.1)
        (_ : FakeEllipticCurve.Rigidification.IsPullbackVia (p.restrictScalars 𝒪) g hg ρ ρ₀'),
        ∃ (ib : ρ₀.Eb.A ⟶ ρ₀'.Eb.A) (_ : ib ≫ ρ₀'.gb = ρ₀.gb ≫ (Iso.refl u₀.1.A).hom) (_ : ib ≫ ρ₀'.Eb.f = ρ₀.Eb.f)
          (uA : ρ₀'.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ₀'.Ab uA) (_ : uA ≫ ρ₀.gA = ρ₀'.gA)
          (i₁ j₁ : ℕ),
          ib ≫ ρ₀'.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧

    (∀ (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ₀' ρ₀'' : FakeEllipticCurve.Rigidification r π A₀ ((p.restrictScalars 𝒪).comp ψS) u₀.1),
        FakeEllipticCurve.Rigidification.IsPullbackVia (p.restrictScalars 𝒪) g hg ρ ρ₀' →
        FakeEllipticCurve.Rigidification.IsPullbackVia (p.restrictScalars 𝒪) g hg ρ' ρ₀'' →
        (∃ (ib : ρ₀.Eb.A ⟶ ρ₀'.Eb.A) (_ : ib ≫ ρ₀'.gb = ρ₀.gb ≫ (Iso.refl u₀.1.A).hom) (_ : ib ≫ ρ₀'.Eb.f = ρ₀.Eb.f)
          (uA : ρ₀'.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ₀'.Ab uA) (_ : uA ≫ ρ₀.gA = ρ₀'.gA)
          (i₁ j₁ : ℕ),
          ib ≫ ρ₀'.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
        (∃ (ib : ρ₀.Eb.A ⟶ ρ₀''.Eb.A) (_ : ib ≫ ρ₀''.gb = ρ₀.gb ≫ (Iso.refl u₀.1.A).hom) (_ : ib ≫ ρ₀''.Eb.f = ρ₀.Eb.f)
          (uA : ρ₀''.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ₀''.Ab uA) (_ : uA ≫ ρ₀.gA = ρ₀''.gA)
          (i₁ j₁ : ℕ),
          ib ≫ ρ₀''.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
        FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ ρ') := by
  classical
  refine ⟨?_, ?_⟩
  ·

    have hNb : IsUnit ((N : ℕ) : S ⧸ Ideal.span {algebraMap 𝒪 S π}) := by
      have hr0 : IsNilpotent ((r : ℕ) : S ⧸ Ideal.span {algebraMap 𝒪 S π}) := by
        have hmem : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
        have h1 : ((r : ℕ) : S ⧸ Ideal.span {algebraMap 𝒪 S π}) =
            Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 S π}) (algebraMap 𝒪 S c * algebraMap 𝒪 S π) := by
          rw [← map_mul, hc, map_natCast, map_natCast]
        have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 S π}) (algebraMap 𝒪 S π) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        rw [h1, map_mul, h2, mul_zero]
        exact IsNilpotent.zero
      exact ClassLiftEX.isUnit_natCast_of_isNilpotent_of_coprime hr0
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hrN))

    have hp2' : ∀ s t : S, (p.restrictScalars 𝒪) s = 0 → (p.restrictScalars 𝒪) t = 0 → s * t = 0 := by
      intro s t hs ht
      have hst : s * t ∈ RingHom.ker (p : S →+* S₀) ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul hs ht
      rw [hp2] at hst
      exact (Submodule.mem_bot _).mp hst
    exact FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_squareZero hrN 𝒪 π hunr Onr Λ hΛℤ coord hcoord A₀
      S S₀ (p.restrictScalars 𝒪) hp hp2' ψS hNb u.1 u₀.1 g hg ρ₀

  ·
    intro ρ ρ' ρ₀' ρ₀'' h h' hc' hc''
    have hNb₀ : IsUnit ((N : ℕ) : S₀ ⧸ Ideal.span {algebraMap 𝒪 S₀ π}) := by
      have hr0 : IsNilpotent ((r : ℕ) : S₀ ⧸ Ideal.span {algebraMap 𝒪 S₀ π}) := by
        have hmem : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
        have h1 : ((r : ℕ) : S₀ ⧸ Ideal.span {algebraMap 𝒪 S₀ π}) =
            Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 S₀ π}) (algebraMap 𝒪 S₀ c * algebraMap 𝒪 S₀ π) := by
          rw [← map_mul, hc, map_natCast, map_natCast]
        have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 S₀ π}) (algebraMap 𝒪 S₀ π) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        rw [h1, map_mul, h2, mul_zero]
        exact IsNilpotent.zero
      exact ClassLiftEX.isUnit_natCast_of_isNilpotent_of_coprime hr0
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hrN))

    have c1 : CorrKit.Corr hΛℤ ρ₀ ρ₀' := by
      obtain ⟨ib, h1, h2, uA, h3, h4, i, j, h5⟩ := hc'
      exact ⟨ib, by simpa only [Iso.refl_hom, Category.comp_id] using h1, h2, uA, h3, h4, i, j, h5⟩
    have c2 : CorrKit.Corr hΛℤ ρ₀ ρ₀'' := by
      obtain ⟨ib, h1, h2, uA, h3, h4, i, j, h5⟩ := hc''
      exact ⟨ib, by simpa only [Iso.refl_hom, Category.comp_id] using h1, h2, uA, h3, h4, i, j, h5⟩
    have he : FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ₀' ρ₀'' :=
      CorrKit.equiv_of_corr_of_corr hΛℤ hNb₀ ρ₀ ρ₀' ρ₀'' c1 c2
    exact FakeEllipticCurve.Rigidification.equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot hrN 𝒪 π hunr Onr Λ hΛℤ A₀
      S S₀ (p.restrictScalars 𝒪) hp hp2 ψS u.1 u₀.1 g hg ρ ρ' ρ₀' ρ₀'' h h' he

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot (solution)
