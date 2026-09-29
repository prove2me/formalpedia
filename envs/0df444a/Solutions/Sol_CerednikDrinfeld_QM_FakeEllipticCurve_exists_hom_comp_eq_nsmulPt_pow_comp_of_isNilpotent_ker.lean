-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9a94d151-6cb2-5d06-ab82-05e42ce1f251

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_JacJ1Iface
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

namespace W1Aux

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

theorem eq_of_isHom_of_comp_eq {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀) (hp : Function.Surjective p)
    (hnil : ∃ n : ℕ, RingHom.ker p ^ n = ⊥)
    (E A : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀) (g : E₀.A ⟶ E.A)
    (hg : IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
    (Φ₁ Φ₂ : E.A ⟶ A.A) (hΦ₁ : Φ₁ ≫ A.f = E.f) (hΦ₂ : Φ₂ ≫ A.f = E.f)
    (hh₁ : IsHom E.L A.L Φ₁ hΦ₁) (hh₂ : IsHom E.L A.L Φ₂ hΦ₂) (hagree : g ≫ Φ₁ = g ≫ Φ₂) : Φ₁ = Φ₂ := by
  have key := GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
    S E.f A.f E.L A.L E.comm A.comm E.bundle A.bundle S S₀ p hp hnil (𝟙 _)
    (pullback.fst E.f (𝟙 _) ≫ Φ₁) (pullback.fst E.f (𝟙 _) ≫ Φ₂)
    (by rw [Category.assoc, hΦ₁, pullback.condition]) (by rw [Category.assoc, hΦ₂, pullback.condition])
    (hhom_of_isHom _ _ _ hΦ₁ hh₁ (𝟙 _) rfl (by rw [Category.assoc, hΦ₁, pullback.condition]))
    (hhom_of_isHom _ _ _ hΦ₂ hh₂ (𝟙 _) rfl (by rw [Category.assoc, hΦ₂, pullback.condition]))
    ?hred
  · have := key
    rw [cancel_epi] at this
    exact this
  · have hub' : IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p) ≫ 𝟙 _) := by simpa using hg
    have hfst := hub'.isoPullback_hom_fst
    have KEY : pullback.fst E.f (Spec.map (CommRingCat.ofHom p) ≫ 𝟙 _) ≫ Φ₁ =
        pullback.fst E.f (Spec.map (CommRingCat.ofHom p) ≫ 𝟙 _) ≫ Φ₂ := by
      apply (cancel_epi hub'.isoPullback.hom).mp
      rw [← Category.assoc hub'.isoPullback.hom, hfst, ← Category.assoc hub'.isoPullback.hom, hfst]
      exact hagree
    have hm : pullback.map E.f (Spec.map (CommRingCat.ofHom p) ≫ 𝟙 _) E.f (𝟙 _) (𝟙 E.A)
        (Spec.map (CommRingCat.ofHom p)) (𝟙 _) (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]) ≫
        pullback.fst E.f (𝟙 _) = pullback.fst E.f (Spec.map (CommRingCat.ofHom p) ≫ 𝟙 _) := by
      simp only [pullback.map, pullback.lift_fst, Category.comp_id]
    rw [← Category.assoc, hm, KEY]
    symm
    rw [← Category.assoc, hm]

theorem eq_one_of_mul_self' {X : Scheme.{0}} {h : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R h)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t h) (hx : G.mul t x x = x) :
    x = G.one t := by
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t x) x := by rw [hx]
    _ = G.one t := G.inv_mul_cancel t x

variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmul_val (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

theorem mapPt_nsmul {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (L' : RelativeGroupLaw R f') (u : A ⟶ A') (hu : u ≫ f' = f) (hh : IsHom L L' u hu)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt u hu (L.nsmul t n P) = L'.nsmul t n (mapPt u hu P) := by
  induction n with
  | zero =>
      rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]

      have h := hh t (L.one t) (L.one t)
      rw [L.one_mul] at h
      exact eq_one_of_mul_self' L' t _ h.symm
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hh, ih]

theorem comp_schemeNsmul_of_isHom {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (L' : RelativeGroupLaw R f') (u : A ⟶ A') (hu : u ≫ f' = f) (hh : IsHom L L' u hu) (n : ℕ) :
    u ≫ L'.schemeNsmul n = L.schemeNsmul n ≫ u := by
  have h := congrArg Subtype.val (mapPt_nsmul L L' u hu hh f n RelativeGroupLaw.idPoint)
  rw [mapPt_coe, nsmul_val, nsmul_val, mapPt_coe] at h
  simpa [Category.assoc] using h.symm

end W1Aux

open W1Aux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) (hpn : IsNilpotent (RingHom.ker p)) (hr : IsNilpotent ((r : ℕ) : S))

    (E A : FakeEllipticCurve Λ N S) (E₀ A₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia p E E₀ g)
    (gA : A₀.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia p A A₀ gA)

    (φ₀ : E₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = E₀.f)
    (φ₀_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t E₀.f),
      mapPt φ₀ hφ₀ (E₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q))
    (φ₀_act : ∀ x : ↥Λ, E₀.act x ≫ φ₀ = φ₀ ≫ A₀.act x) :
    ∃ (m : ℕ) (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = A.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ A.act x) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t E₀.f),
        P.1 ≫ g ≫ φ = (nsmulPt A₀.L t (r ^ m) (mapPt φ₀ hφ₀ P)).1 ≫ gA) := by
  classical
  letI instAlg : Algebra S S₀ := p.toAlgebra
  have halg : algebraMap S S₀ = p := rfl
  obtain ⟨k, hk⟩ := hr
  have hN : ((r ^ k : ℕ) : S) = 0 := by push_cast; exact hk
  obtain ⟨n, hn⟩ := hpn
  have hμ : RingHom.ker (algebraMap S S₀) ^ (n + 1) = ⊥ := by
    rw [halg, pow_succ, hn, zero_mul]; rfl
  obtain ⟨hgsq, hgL, hgact, -⟩ := hg
  obtain ⟨hgAsq, hgAL, hgAact, -⟩ := hgA

  obtain ⟨F, hF, hFhom, hFred⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
      S S₀ hp (r ^ k) hN n hμ E.f E.L E.comm E.bundle A.f A.L A.comm A.bundle
      E₀.f E₀.L g hgsq hgL A₀.f A₀.L gA hgAsq hgAL φ₀ hφ₀ (fun t P Q => congrArg Subtype.val (φ₀_mul t P Q))
  rw [← pow_mul] at hFred
  have hFhom' : IsHom E.L A.L F hF := fun t P Q => Subtype.ext (hFhom t P Q)
  have hφ₀hom : IsHom E₀.L A₀.L φ₀ hφ₀ := fun t P Q => φ₀_mul t P Q
  refine ⟨k * n, F, hF, fun t P Q => hFhom' t P Q, ?_, ?_⟩
  ·
    intro x
    have hΦ₁ : (E.act x ≫ F) ≫ A.f = E.f := by rw [Category.assoc, hF, E.act_over]
    have hΦ₂ : (F ≫ A.act x) ≫ A.f = E.f := by rw [Category.assoc, A.act_over, hF]
    refine eq_of_isHom_of_comp_eq p hp ⟨n + 1, halg ▸ hμ⟩ E A E₀ g hgsq _ _ hΦ₁ hΦ₂
      (IsHom.comp (IsHom.of_act E x) hFhom' hΦ₁) (IsHom.comp hFhom' (IsHom.of_act A x) hΦ₂) ?_

    rw [← Category.assoc, ← hgact x, Category.assoc, hFred, ← Category.assoc g F, hFred]
    simp only [Category.assoc]
    rw [← hgAact x, ← Category.assoc (A₀.L.schemeNsmul (r ^ (k * n))) (A₀.act x) gA,
      ← comp_schemeNsmul_of_isHom A₀.L A₀.L (A₀.act x) (A₀.act_over x) (IsHom.of_act A₀ x) (r ^ (k * n)),
      Category.assoc, ← Category.assoc φ₀ (A₀.act x), ← φ₀_act x]
    simp only [Category.assoc]
  ·
    intro T t P
    rw [hFred, nsmulPt_eq_nsmul, nsmul_val, mapPt_coe]
    simp only [Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker (solution)
