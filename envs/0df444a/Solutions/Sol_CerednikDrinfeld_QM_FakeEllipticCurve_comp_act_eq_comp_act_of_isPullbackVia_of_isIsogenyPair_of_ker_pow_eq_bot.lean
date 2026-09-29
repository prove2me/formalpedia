-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c820d99f-7d07-5cc8-85d1-f007eb0e68b1

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
open scoped Quaternion

namespace RC12

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

end RC12

open RC12

theorem RC12.surjective_and_isNilpotent_ker
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪)
    (B B₀ : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀] [Algebra B B₀] [IsScalarTower 𝒪 B B₀]
    (hsurj : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (Bb B₀b : Type) [CommRing Bb] [CommRing B₀b] (qB : B →+* Bb) (qB₀ : B₀ →+* B₀b) (f₀₀ : Bb →+* B₀b)
    (hqB : RingHom.ker qB = Ideal.span {algebraMap 𝒪 B π}) (hqBs : Function.Surjective qB)
    (hqB₀ : RingHom.ker qB₀ = Ideal.span {algebraMap 𝒪 B₀ π}) (hqB₀s : Function.Surjective qB₀)
    (hsq : f₀₀.comp qB = qB₀.comp (algebraMap B B₀)) :
    Function.Surjective f₀₀ ∧ ∃ n : ℕ, RingHom.ker f₀₀ ^ n = ⊥ := by
  constructor
  · intro y
    obtain ⟨b₀, rfl⟩ := hqB₀s y
    obtain ⟨b, rfl⟩ := hsurj b₀
    exact ⟨qB b, by rw [← RingHom.comp_apply, hsq, RingHom.comp_apply]⟩
  · obtain ⟨n, hn⟩ := hker
    refine ⟨n, ?_⟩

    have hle : RingHom.ker f₀₀ ≤ Ideal.map qB (RingHom.ker (algebraMap B B₀)) := by
      intro x hx
      obtain ⟨s, rfl⟩ := hqBs x
      rw [RingHom.mem_ker, ← RingHom.comp_apply, hsq, RingHom.comp_apply, ← RingHom.mem_ker, hqB₀,
        Ideal.mem_span_singleton'] at hx
      obtain ⟨c₀, hc₀⟩ := hx
      obtain ⟨c, rfl⟩ := hsurj c₀
      have hmem : s - c * algebraMap 𝒪 B π ∈ RingHom.ker (algebraMap B B₀) := by
        rw [RingHom.mem_ker, map_sub, map_mul, ← hc₀, sub_eq_zero]
        congr 1
        exact IsScalarTower.algebraMap_apply 𝒪 B B₀ π
      have hπ : qB (c * algebraMap 𝒪 B π) = 0 := by
        rw [← RingHom.mem_ker, hqB]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      have : qB s = qB (s - c * algebraMap 𝒪 B π) := by rw [map_sub, hπ, sub_zero]
      rw [this]
      exact Ideal.mem_map_of_mem _ hmem
    rw [eq_bot_iff]
    calc RingHom.ker f₀₀ ^ n ≤ (Ideal.map qB (RingHom.ker (algebraMap B B₀))) ^ n := Ideal.pow_right_mono hle n
      _ = Ideal.map qB (RingHom.ker (algebraMap B B₀) ^ n) := (Ideal.map_pow qB _ n).symm
      _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]

theorem RC12.unique
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {r : ℕ}
    (Bb B₀b : Type) [CommRing Bb] [CommRing B₀b] (f₀₀ : Bb →+* B₀b) (hf : Function.Surjective f₀₀)
    (hnil : ∃ n : ℕ, RingHom.ker f₀₀ ^ n = ⊥)
    (Eb : FakeEllipticCurve Λ N Bb) (E₀b : FakeEllipticCurve Λ N B₀b) (Ab : FakeEllipticCurve Λ N Bb)
    (u : E₀b.A ⟶ Eb.A) (hu' : FakeEllipticCurve.IsPullbackVia f₀₀ Eb E₀b u)
    (d₁ d₂ : ℕ) (φ₁ φ₂ : Eb.A ⟶ Ab.A) (φ₁' φ₂' : Ab.A ⟶ Eb.A)
    (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d₁) Eb Ab φ₁ φ₁') (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d₂) Eb Ab φ₂ φ₂')
    (i j : ℕ)
    (hagree : u ≫ φ₁ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = u ≫ φ₂ ≫ Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    φ₁ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = φ₂ ≫ Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  set cI : ↥Λ := ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcI
  set cJ : ↥Λ := ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcJ
  obtain ⟨hφo₁, -, haddφ₁, -, -, -, -⟩ := hp₁
  obtain ⟨hφo₂, -, haddφ₂, -, -, -, -⟩ := hp₂
  obtain ⟨hub, -, -, -⟩ := hu'

  have hΦ₁ : (φ₁ ≫ Ab.act cI) ≫ Ab.f = Eb.f := by simp only [Category.assoc, Ab.act_over]; exact hφo₁
  have hΦ₂ : (φ₂ ≫ Ab.act cJ) ≫ Ab.f = Eb.f := by simp only [Category.assoc, Ab.act_over]; exact hφo₂
  have hh₁ : IsHom Eb.L Ab.L (φ₁ ≫ Ab.act cI) hΦ₁ := IsHom.comp haddφ₁ (IsHom.of_act Ab cI) hΦ₁
  have hh₂ : IsHom Eb.L Ab.L (φ₂ ≫ Ab.act cJ) hΦ₂ := IsHom.comp haddφ₂ (IsHom.of_act Ab cJ) hΦ₂
  have hagree' : u ≫ (φ₁ ≫ Ab.act cI) = u ≫ (φ₂ ≫ Ab.act cJ) := hagree

  have key := GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
    Bb Eb.f Ab.f Eb.L Ab.L Eb.comm Ab.comm Eb.bundle Ab.bundle Bb B₀b f₀₀ hf hnil (𝟙 _)
    (pullback.fst Eb.f (𝟙 _) ≫ (φ₁ ≫ Ab.act cI)) (pullback.fst Eb.f (𝟙 _) ≫ (φ₂ ≫ Ab.act cJ))
    (by rw [Category.assoc, hΦ₁, pullback.condition]) (by rw [Category.assoc, hΦ₂, pullback.condition])
    (hhom_of_isHom _ _ _ hΦ₁ hh₁ (𝟙 _) rfl (by rw [Category.assoc, hΦ₁, pullback.condition]))
    (hhom_of_isHom _ _ _ hΦ₂ hh₂ (𝟙 _) rfl (by rw [Category.assoc, hΦ₂, pullback.condition]))
    ?hred
  · have := key
    rw [cancel_epi] at this
    exact this
  · have hub' : IsPullback u E₀b.f Eb.f (Spec.map (CommRingCat.ofHom f₀₀) ≫ 𝟙 _) := by simpa using hub
    have hfst := hub'.isoPullback_hom_fst
    have KEY : pullback.fst Eb.f (Spec.map (CommRingCat.ofHom f₀₀) ≫ 𝟙 _) ≫ (φ₁ ≫ Ab.act cI) =
        pullback.fst Eb.f (Spec.map (CommRingCat.ofHom f₀₀) ≫ 𝟙 _) ≫ (φ₂ ≫ Ab.act cJ) := by
      apply (cancel_epi hub'.isoPullback.hom).mp
      rw [← Category.assoc hub'.isoPullback.hom, hfst, ← Category.assoc hub'.isoPullback.hom, hfst]
      exact hagree'
    have hm : pullback.map Eb.f (Spec.map (CommRingCat.ofHom f₀₀) ≫ 𝟙 _) Eb.f (𝟙 _) (𝟙 Eb.A)
        (Spec.map (CommRingCat.ofHom f₀₀)) (𝟙 _) (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]) ≫
        pullback.fst Eb.f (𝟙 _) = pullback.fst Eb.f (Spec.map (CommRingCat.ofHom f₀₀) ≫ 𝟙 _) := by
      simp only [pullback.map, pullback.lift_fst, Category.comp_id]
    rw [← Category.assoc, hm, KEY]
    symm
    rw [← Category.assoc, hm]

theorem RC12.unique_exists
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {r : ℕ}
    (Bb B₀b : Type) [CommRing Bb] [CommRing B₀b] (f₀₀ : Bb →+* B₀b) (hf : Function.Surjective f₀₀)
    (hnil : ∃ n : ℕ, RingHom.ker f₀₀ ^ n = ⊥)
    (Eb : FakeEllipticCurve Λ N Bb) (E₀b : FakeEllipticCurve Λ N B₀b) (Ab : FakeEllipticCurve Λ N Bb)
    (u : E₀b.A ⟶ Eb.A) (hu' : FakeEllipticCurve.IsPullbackVia f₀₀ Eb E₀b u) :
    ∀ (d₁ d₂ : ℕ) (φ₁ φ₂ : Eb.A ⟶ Ab.A) (φ₁' φ₂' : Ab.A ⟶ Eb.A),
        FakeEllipticCurve.IsIsogenyPair (r ^ d₁) Eb Ab φ₁ φ₁' → FakeEllipticCurve.IsIsogenyPair (r ^ d₂) Eb Ab φ₂ φ₂' →
        (∃ i j : ℕ, u ≫ φ₁ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = u ≫ φ₂ ≫ Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
        ∃ i j : ℕ, φ₁ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = φ₂ ≫ Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  intro d₁ d₂ φ₁ φ₂ φ₁' φ₂' hp₁ hp₂ hagree0
  obtain ⟨i, j, hagree⟩ := hagree0
  exact ⟨i, j, RC12.unique hΛℤ Bb B₀b f₀₀ hf hnil Eb E₀b Ab u hu' d₁ d₂ φ₁ φ₂ φ₁' φ₂' hp₁ hp₂ i j hagree⟩

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (r : ℕ)
    (Bb B₀b : Type) [CommRing Bb] [CommRing B₀b] (f₀₀ : Bb →+* B₀b) (hf : Function.Surjective f₀₀)
    (hnil : ∃ n : ℕ, RingHom.ker f₀₀ ^ n = ⊥)
    (Eb : FakeEllipticCurve Λ N Bb) (E₀b : FakeEllipticCurve Λ N B₀b) (Ab : FakeEllipticCurve Λ N Bb)
    (u : E₀b.A ⟶ Eb.A) (hu : FakeEllipticCurve.IsPullbackVia f₀₀ Eb E₀b u)
    (d₁ d₂ : ℕ) (φ₁ φ₂ : Eb.A ⟶ Ab.A) (φ₁' φ₂' : Ab.A ⟶ Eb.A)
    (h₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d₁) Eb Ab φ₁ φ₁') (h₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d₂) Eb Ab φ₂ φ₂')
    (i j : ℕ)
    (hagree : u ≫ φ₁ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = u ≫ φ₂ ≫ Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    φ₁ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = φ₂ ≫ Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  exact RC12.unique hΛℤ Bb B₀b f₀₀ hf hnil Eb E₀b Ab u hu d₁ d₂ φ₁ φ₂ φ₁' φ₂' h₁ h₂ i j hagree

end S_CerednikDrinfeld_QM_FakeEllipticCurve_comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot (solution)
