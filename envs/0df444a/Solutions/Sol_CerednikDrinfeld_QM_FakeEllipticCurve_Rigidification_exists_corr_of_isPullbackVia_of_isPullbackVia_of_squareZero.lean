-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isPullbackVia_of_isPullbackVia_of_squareZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/cfd1a7a5-0831-5fc7-b5ba-3712a5aaf180

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia_of_squareZero
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
open scoped Quaternion

namespace P2RC1

universe u

variable {R : Type} [CommRing R]

theorem mul_val_congr {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (P Q : SchemeHomOver t f) :
    (L.mul t P Q).1 = (L.mul t' ⟨P.1, h ▸ P.2⟩ ⟨Q.1, h ▸ Q.2⟩).1 := by
  subst h; rfl

def IsHom {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (Φ : A ⟶ A') (hΦ : Φ ≫ f' = f) : Prop :=
  ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    mapPt Φ hΦ (L.mul t P Q) = L'.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)

theorem IsHom.comp {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)}
    {L : RelativeGroupLaw R f} {L' : RelativeGroupLaw R f'} {L'' : RelativeGroupLaw R f''}
    {Φ : A ⟶ A'} {hΦ : Φ ≫ f' = f} {Ψ : A' ⟶ A''} {hΨ : Ψ ≫ f'' = f'}
    (h1 : IsHom L L' Φ hΦ) (h2 : IsHom L' L'' Ψ hΨ) (hc : (Φ ≫ Ψ) ≫ f'' = f) :
    IsHom L L'' (Φ ≫ Ψ) hc := by
  intro T t P Q
  have e : ∀ X : SchemeHomOver t f, mapPt (Φ ≫ Ψ) hc X = mapPt Ψ hΨ (mapPt Φ hΦ X) := fun X =>
    Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  rw [e, e, e, h1, h2]

theorem IsHom.of_isPullbackVia_id {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (E E' : FakeEllipticCurve Λ N R) (g : E'.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (RingHom.id R) E E' g)
    (hgo : g ≫ E.f = E'.f) : IsHom E'.L E.L g hgo := by
  obtain ⟨hsq, hmul, -, -⟩ := hg
  intro T t P Q
  apply Subtype.ext
  have hid : t ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) = t := by simp
  rw [mapPt_coe, hmul t P Q, mul_val_congr E.L hid]
  rfl

theorem IsHom.of_act {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N R) (x : ↥Λ) :
    IsHom E.L E.L (E.act x) (E.act_over x) :=
  fun t P Q => E.act_hom x t P Q

theorem hhom_of_isHom {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (Φ : A ⟶ A') (hΦ : Φ ≫ f' = f) (hh : IsHom L L' Φ hΦ)
    (s : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) (hs : s = 𝟙 _)
    (hφ : (pullback.fst f s ≫ Φ) ≫ f' = pullback.snd f s ≫ s) :
    ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ (pullback.fst f s ≫ Φ) =
          (L'.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ (pullback.fst f s ≫ Φ), by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ (pullback.fst f s ≫ Φ), by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1 := by
  intro T t' P Q
  have e : ∀ (X : SchemeHomOver (t' ≫ s) f)
      (pf : (pullback.lift X.1 t' X.2 ≫ (pullback.fst f s ≫ Φ)) ≫ f' = t' ≫ s),
      (⟨pullback.lift X.1 t' X.2 ≫ (pullback.fst f s ≫ Φ), pf⟩ : SchemeHomOver (t' ≫ s) f') = mapPt Φ hΦ X := by
    intro X pf; apply Subtype.ext; simp only [mapPt_coe, pullback.lift_fst_assoc]
  rw [e, e, pullback.lift_fst_assoc, ← hh]
  rfl

end P2RC1

open P2RC1

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}

    {B : Type} [CommRing B] [Algebra 𝒪 B] {B₀ : Type} [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
    (hp : Function.Surjective p) (hp2 : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (ψ : Onr →ₐ[𝒪] B)

    (hNb : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))

    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g)

    (ϱ₁ ϱ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ϱ₁₀ ϱ₂₀ : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀)
    (h₁ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ϱ₁ ϱ₁₀)
    (h₂ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ϱ₂ ϱ₂₀)

    (h₀ : ∃ (ib : ϱ₁₀.Eb.A ⟶ ϱ₂₀.Eb.A) (_ : ib ≫ ϱ₂₀.gb = ϱ₁₀.gb) (_ : ib ≫ ϱ₂₀.Eb.f = ϱ₁₀.Eb.f)
      (uA : ϱ₂₀.Ab.A ⟶ ϱ₁₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ₁₀.Ab ϱ₂₀.Ab uA) (_ : uA ≫ ϱ₁₀.gA = ϱ₂₀.gA)
      (i j : ℕ),
      ib ≫ ϱ₂₀.φ ≫ uA ≫ ϱ₁₀.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ₁₀.φ ≫ ϱ₁₀.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (ib : ϱ₁.Eb.A ⟶ ϱ₂.Eb.A) (_ : ib ≫ ϱ₂.gb = ϱ₁.gb) (_ : ib ≫ ϱ₂.Eb.f = ϱ₁.Eb.f)
      (uA : ϱ₂.Ab.A ⟶ ϱ₁.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ₁.Ab ϱ₂.Ab uA) (_ : uA ≫ ϱ₁.gA = ϱ₂.gA)
      (i j : ℕ),
      ib ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ₁.φ ≫ ϱ₁.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical
  obtain ⟨ib₀, hib₀g, hib₀f, uA₀, huA₀, huA₀g, i, j, h₀eq⟩ := h₀
  obtain ⟨ub₁, uB₁, hub₁, hub₁g, huB₁, huB₁g, hd₁, hsq₁⟩ := h₁
  obtain ⟨ub₂, uB₂, hub₂, hub₂g, huB₂, huB₂g, hd₂, hsq₂⟩ := h₂

  obtain ⟨ib, hibg, hibf, hib⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) hNb E ϱ₂.Eb ϱ₂.gb ϱ₂.isPullback_Eb ϱ₁.Eb ϱ₁.gb ϱ₁.isPullback_Eb
  obtain ⟨uA, huAg, huAf, huA⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hNb A₀ ϱ₁.Ab ϱ₁.gA ϱ₁.isPullback_Ab ϱ₂.Ab ϱ₂.gA ϱ₂.isPullback_Ab
  refine ⟨ib, hibg, hibf, uA, huA, huAg, i, j, ?_⟩

  set cI : ↥Λ := ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcI
  set cJ : ↥Λ := ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcJ

  obtain ⟨hpbE₂, -, -, -⟩ := ϱ₂.isPullback_Eb
  obtain ⟨hpbA₁, -, -, -⟩ := ϱ₁.isPullback_Ab
  obtain ⟨hub₁sq, -, -, -⟩ := hub₁
  obtain ⟨hub₂sq, -, -, -⟩ := hub₂
  obtain ⟨huB₁sq, -, huB₁act, -⟩ := huB₁
  obtain ⟨huB₂sq, -, -, -⟩ := huB₂
  obtain ⟨huA₀sq, -, -, -⟩ := huA₀
  obtain ⟨hφo₁, -, haddφ₁, -, -, -, -⟩ := ϱ₁.isIsogenyPair
  obtain ⟨hφo₂, -, haddφ₂, -, -, -, -⟩ := ϱ₂.isIsogenyPair

  have hΦ₁ : (ib ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI) ≫ ϱ₁.Ab.f = ϱ₁.Eb.f := by
    simp only [Category.assoc, ϱ₁.Ab.act_over, huAf]; rw [hφo₂, hibf]
  have hΦ₂ : (ϱ₁.φ ≫ ϱ₁.Ab.act cJ) ≫ ϱ₁.Ab.f = ϱ₁.Eb.f := by
    simp only [Category.assoc, ϱ₁.Ab.act_over]; exact hφo₁

  have hcompat_b : ub₁ ≫ ib = ib₀ ≫ ub₂ := by
    apply hpbE₂.hom_ext
    · rw [Category.assoc, hibg, hub₁g, Category.assoc, hub₂g, ← Category.assoc, hib₀g]
    · rw [Category.assoc, hibf, hub₁sq.w, Category.assoc, hub₂sq.w, ← Category.assoc, hib₀f]
  have huA₀f : uA₀ ≫ ϱ₁₀.Ab.f = ϱ₂₀.Ab.f := by
    have := huA₀sq.w; simpa using this
  have hcompat_A : uB₂ ≫ uA = uA₀ ≫ uB₁ := by
    apply hpbA₁.hom_ext
    · rw [Category.assoc, huAg, huB₂g, Category.assoc, huB₁g, huA₀g]
    · rw [Category.assoc, huAf, huB₂sq.w, Category.assoc, huB₁sq.w, ← Category.assoc, huA₀f]
  have hagree : ub₁ ≫ (ib ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI) = ub₁ ≫ (ϱ₁.φ ≫ ϱ₁.Ab.act cJ) := by
    calc ub₁ ≫ (ib ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI)
        = (ub₁ ≫ ib) ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI := by simp only [Category.assoc]
      _ = ib₀ ≫ (ub₂ ≫ ϱ₂.φ) ≫ uA ≫ ϱ₁.Ab.act cI := by rw [hcompat_b]; simp only [Category.assoc]
      _ = ib₀ ≫ ϱ₂₀.φ ≫ (uB₂ ≫ uA) ≫ ϱ₁.Ab.act cI := by rw [hsq₂]; simp only [Category.assoc]
      _ = ib₀ ≫ ϱ₂₀.φ ≫ uA₀ ≫ (uB₁ ≫ ϱ₁.Ab.act cI) := by rw [hcompat_A]; simp only [Category.assoc]
      _ = (ib₀ ≫ ϱ₂₀.φ ≫ uA₀ ≫ ϱ₁₀.Ab.act cI) ≫ uB₁ := by rw [← huB₁act cI]; simp only [Category.assoc]
      _ = (ϱ₁₀.φ ≫ ϱ₁₀.Ab.act cJ) ≫ uB₁ := by rw [h₀eq]
      _ = ϱ₁₀.φ ≫ uB₁ ≫ ϱ₁.Ab.act cJ := by rw [Category.assoc, huB₁act cJ]
      _ = ub₁ ≫ (ϱ₁.φ ≫ ϱ₁.Ab.act cJ) := by rw [← Category.assoc, ← hsq₁, Category.assoc]

  have hhib : IsHom ϱ₁.Eb.L ϱ₂.Eb.L ib hibf := IsHom.of_isPullbackVia_id _ _ ib hib hibf
  have hhuA : IsHom ϱ₂.Ab.L ϱ₁.Ab.L uA huAf := IsHom.of_isPullbackVia_id _ _ uA huA huAf
  have hA1 : (uA ≫ ϱ₁.Ab.act cI) ≫ ϱ₁.Ab.f = ϱ₂.Ab.f := by
    simp only [Category.assoc, ϱ₁.Ab.act_over, huAf]
  have hA2 : (ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI) ≫ ϱ₁.Ab.f = ϱ₂.Eb.f := by
    simp only [Category.assoc, ϱ₁.Ab.act_over, huAf]; exact hφo₂
  have hh_uAact : IsHom ϱ₂.Ab.L ϱ₁.Ab.L (uA ≫ ϱ₁.Ab.act cI) hA1 := IsHom.comp hhuA (IsHom.of_act ϱ₁.Ab cI) hA1
  have hh_φuAact : IsHom ϱ₂.Eb.L ϱ₁.Ab.L (ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI) hA2 := IsHom.comp haddφ₂ hh_uAact hA2
  have hh₁ : IsHom ϱ₁.Eb.L ϱ₁.Ab.L (ib ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI) hΦ₁ := IsHom.comp hhib hh_φuAact hΦ₁
  have hh₂ : IsHom ϱ₁.Eb.L ϱ₁.Ab.L (ϱ₁.φ ≫ ϱ₁.Ab.act cJ) hΦ₂ :=
    IsHom.comp haddφ₁ (IsHom.of_act ϱ₁.Ab cJ) hΦ₂

  have hpbsurj : Function.Surjective
      (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
          (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
              exact Ideal.subset_span rfl))))) :=
    Ideal.quotientMap_surjective hp
  have hpbnil : ∃ n : ℕ, RingHom.ker
      (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
          (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
              exact Ideal.subset_span rfl))))) ^ n = ⊥ := by
    refine ⟨2, ?_⟩
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx hy
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    obtain ⟨c', rfl⟩ := hp c
    obtain ⟨d', rfl⟩ := hp d
    have hπ' : (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π := p.commutes π
    have hs0 : p (s - c' * algebraMap 𝒪 B π) = 0 := by
      rw [map_sub, map_mul, AlgHom.commutes, sub_eq_zero]; exact hc.symm
    have ht0 : p (t - d' * algebraMap 𝒪 B π) = 0 := by
      rw [map_sub, map_mul, AlgHom.commutes, sub_eq_zero]; exact hd.symm
    have hst := hp2 _ _ hs0 ht0
    show Ideal.Quotient.mk _ s * Ideal.Quotient.mk _ t ∈ (⊥ : Ideal (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨(s - c' * algebraMap 𝒪 B π) * d' + c' * t, ?_⟩
    have : s * t = (s - c' * algebraMap 𝒪 B π) * (t - d' * algebraMap 𝒪 B π)
        + ((s - c' * algebraMap 𝒪 B π) * d' + c' * t) * algebraMap 𝒪 B π := by ring
    rw [this, hst, zero_add]

  have hs : (𝟙 (Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))) = 𝟙 _ := rfl
  have key := GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
    (B ⧸ Ideal.span {algebraMap 𝒪 B π}) ϱ₁.Eb.f ϱ₁.Ab.f ϱ₁.Eb.L ϱ₁.Ab.L ϱ₁.Eb.comm ϱ₁.Ab.comm ϱ₁.Eb.bundle ϱ₁.Ab.bundle
    (B ⧸ Ideal.span {algebraMap 𝒪 B π}) (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π}) _ hpbsurj hpbnil (𝟙 _)
    (pullback.fst ϱ₁.Eb.f (𝟙 _) ≫ (ib ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI))
    (pullback.fst ϱ₁.Eb.f (𝟙 _) ≫ (ϱ₁.φ ≫ ϱ₁.Ab.act cJ))
    (by rw [Category.assoc, hΦ₁, pullback.condition])
    (by rw [Category.assoc, hΦ₂, pullback.condition])
    (hhom_of_isHom _ _ _ hΦ₁ hh₁ (𝟙 _) rfl (by rw [Category.assoc, hΦ₁, pullback.condition]))
    (hhom_of_isHom _ _ _ hΦ₂ hh₂ (𝟙 _) rfl (by rw [Category.assoc, hΦ₂, pullback.condition]))
    ?hred
  ·
    have := key
    rw [cancel_epi] at this
    exact this
  ·
    have hub₁sq' : IsPullback ub₁ ϱ₁₀.Eb.f ϱ₁.Eb.f ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
                exact Ideal.subset_span rfl))))))) ≫ 𝟙 _) := by
      simpa using hub₁sq
    have hfst := hub₁sq'.isoPullback_hom_fst
    have KEY : pullback.fst ϱ₁.Eb.f ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
                exact Ideal.subset_span rfl))))))) ≫ 𝟙 _) ≫ (ib ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act cI) =
        pullback.fst ϱ₁.Eb.f ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
                exact Ideal.subset_span rfl))))))) ≫ 𝟙 _) ≫ (ϱ₁.φ ≫ ϱ₁.Ab.act cJ) := by
      apply (cancel_epi hub₁sq'.isoPullback.hom).mp
      rw [← Category.assoc hub₁sq'.isoPullback.hom, hfst, ← Category.assoc hub₁sq'.isoPullback.hom, hfst]
      exact hagree
    have hm : pullback.map ϱ₁.Eb.f ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
                exact Ideal.subset_span rfl))))))) ≫ 𝟙 _) ϱ₁.Eb.f (𝟙 _) (𝟙 ϱ₁.Eb.A) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
                exact Ideal.subset_span rfl))))))) (𝟙 _)
          (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]) ≫ pullback.fst ϱ₁.Eb.f (𝟙 _) =
        pullback.fst ϱ₁.Eb.f ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀)
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
                exact Ideal.subset_span rfl))))))) ≫ 𝟙 _) := by
      simp only [pullback.map, pullback.lift_fst, Category.comp_id]
    rw [← Category.assoc, hm, KEY]
    symm
    rw [← Category.assoc, hm]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia_of_squareZero
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia_of_squareZero (solution)
