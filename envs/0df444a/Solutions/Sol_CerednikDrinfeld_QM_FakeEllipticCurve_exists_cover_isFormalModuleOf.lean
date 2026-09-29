-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_isFormalModuleOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/99a3c4ac-1104-5f04-b1d6-79b1f22db196

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_two_of_isFormalGroupAlong
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_of_isFormalCoordinates
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_isFormalModuleOf
p2m_attr_erase "instance" "AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian CerednikDrinfeld.QM"

noncomputable section

namespace PABridge

variable {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')

abbrev paBase (C : Type) [CommRing C] [Algebra R' C] : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap R' C).comp φ))

theorem specOver_comp (C : Type) [CommRing C] [Algebra R' C] :
    Scheme.specOver (𝒪 := R') C ≫ Spec.map (CommRingCat.ofHom φ) = paBase φ C := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

section Congr

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem one_val_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') :
    (L.one t).1 = (L.one t').1 := by
  subst h; rfl

theorem mul_val_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (hx : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [hx]
    _ = L.one t := L.inv_mul_cancel t x

theorem isInfinitesimal_iff_val {C : Type} [CommRing C] [Algebra S C] (J : Ideal C)
    (P : SchemeHomOver (Scheme.specOver (𝒪 := S) C) f) :
    L.IsInfinitesimal J P ↔
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 =
        (L.one (Scheme.specOver (𝒪 := S) (C ⧸ J))).1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem specMap_mk_comp_specOver {C : Type} [CommRing C] [Algebra S C] (J : Ideal C) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Scheme.specOver (𝒪 := S) C =
      Scheme.specOver (𝒪 := S) (C ⧸ J) :=
  Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ S J)

end Congr

section Nil

variable {C : Type} [CommRing C]

theorem exists_pow_succ_eq_bot {J : Ideal C} (hJ : IsNilpotent J) : ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [pow_succ, hn, zero_mul]; rfl⟩

theorem isNilpotent_of_mem {J : Ideal C} (hJ : IsNilpotent J) {x : C} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at this
  exact (Submodule.mem_bot C).1 this

theorem isNilpotent_span_range {n : ℕ} (s : Fin n → C) (hs : ∀ i, IsNilpotent (s i)) :
    IsNilpotent (Ideal.span (Set.range s)) := by
  classical
  have hle : Ideal.span (Set.range s) ≤ (⊥ : Ideal C).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hs i
    exact ⟨k, by rw [hk]; exact Submodule.zero_mem _⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (Submodule.fg_span (Set.finite_range s))
  exact ⟨k, le_bot_iff.1 hk⟩

theorem isAdicComplete_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) : IsAdicComplete J C := by
  obtain ⟨n, hn⟩ := hJ
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx n
    rw [hn] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f n, fun m => by
    by_cases hm : m ≤ n
    · exact hf hm
    · push Not at hm
      have h1 : f n ≡ f m [SMOD (J ^ n • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = n + (m - n) by omega, pow_add, hn, zero_mul]; simp
      have h3 : (J ^ n • ⊤ : Submodule C C) = ⊥ := by rw [hn]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem aeval_mem_of_coeff_zero {S : Type} [CommRing S] [Algebra S C] {σ : Type} (J : Ideal C)
    (p : MvPolynomial σ S) (hp : p.coeff 0 = 0) (a : σ → C) (ha : ∀ i, a i ∈ J) : MvPolynomial.aeval a p ∈ J := by
  classical
  rw [p.as_sum, map_sum]
  refine Ideal.sum_mem _ fun d _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hd0 : d = 0
  · subst hd0
    rw [hp, map_zero, zero_mul]
    exact J.zero_mem
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd0 (Finsupp.ext fun s => by simpa using h s)
    refine Ideal.mul_mem_left _ _ ?_
    rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ (Finsupp.mem_support_iff.mpr hs)]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    exact Ideal.mul_mem_left _ _ (ha s)

theorem nilEval_mem {S : Type} [CommRing S] [Algebra S C] {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal C)
    (n : ℕ) (φ : MvPowerSeries σ S) (hφ : MvPowerSeries.constantCoeff φ = 0) (a : σ → C) (ha : ∀ i, a i ∈ J) :
    MvFormalGroup.nilEval n φ a ∈ J := by
  unfold MvFormalGroup.nilEval
  refine aeval_mem_of_coeff_zero J _ ?_ a ha
  rw [MvPowerSeries.coeff_trunc', if_pos (Finsupp.le_def.2 fun _ => Nat.zero_le _),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]

end Nil

section Transport

variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R')}
  (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))

include hg in
theorem ext_of_comp_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} (P Q : SchemeHomOver t f')
    (h : P.1 ≫ g = Q.1 ≫ g) : P = Q :=
  Subtype.ext (hg.hom_ext h (by rw [P.2, Q.2]))

def down {C : Type} [CommRing C] [Algebra R' C] (P : SchemeHomOver (Scheme.specOver (𝒪 := R') C) f') :
    SchemeHomOver (paBase φ C) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2, specOver_comp]⟩

@[scoped simp] theorem down_val {C : Type} [CommRing C] [Algebra R' C]
    (P : SchemeHomOver (Scheme.specOver (𝒪 := R') C) f') : (down φ g hg P).1 = P.1 ≫ g := rfl

def up {C : Type} [CommRing C] [Algebra R' C] (P : SchemeHomOver (paBase φ C) f) :
    SchemeHomOver (Scheme.specOver (𝒪 := R') C) f' :=
  ⟨hg.lift P.1 (Scheme.specOver (𝒪 := R') C) (by rw [P.2, specOver_comp]), hg.lift_snd _ _ _⟩

@[scoped simp] theorem up_val_comp {C : Type} [CommRing C] [Algebra R' C] (P : SchemeHomOver (paBase φ C) f) :
    (up φ g hg P).1 ≫ g = P.1 :=
  hg.lift_fst _ _ _

theorem up_down {C : Type} [CommRing C] [Algebra R' C] (P : SchemeHomOver (Scheme.specOver (𝒪 := R') C) f') :
    up φ g hg (down φ g hg P) = P :=
  ext_of_comp_eq φ g hg _ _ (by rw [up_val_comp, down_val])

variable (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R' f')

def IsMulCompat : Prop :=
  ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ g =
      (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1

variable {L L'}

theorem one_val_comp (hmul : IsMulCompat φ g hg L L') {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (L'.one t').1 ≫ g = (L.one (t' ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  have h := hmul t' (L'.one t') (L'.one t')
  rw [L'.mul_one] at h
  have hx := eq_one_of_mul_self L _
    (⟨(L'.one t').1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, (L'.one t').2]⟩ :
      SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f)
    (Subtype.ext h.symm)
  exact congrArg Subtype.val hx

theorem quotBase_eq (C : Type) [CommRing C] [Algebra R' C] (J : Ideal C) :
    Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp ((algebraMap R' C).comp φ))) =
      Scheme.specOver (𝒪 := R') (C ⧸ J) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [specOver_comp]

end Transport

section Bridge

variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R')}
  {L : RelativeGroupLaw R f} {L' : RelativeGroupLaw R' f'}
  {g : A' ⟶ A} {hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))}
  {n : ℕ} {F : MvFormalGroup n R'}
  (θ : ∀ (C : Type) [CommRing C] [Algebra R' C] (J : Ideal C) [IsAdicComplete J C],
    F.Points C J → SchemeHomOver (paBase φ C) f)

def IsKernelOfReductionData (L : RelativeGroupLaw R f) (F : MvFormalGroup n R')
    (θ : ∀ (C : Type) [CommRing C] [Algebra R' C] (J : Ideal C) [IsAdicComplete J C],
      F.Points C J → SchemeHomOver (paBase φ C) f) : Prop :=
  ∀ (C : Type) [CommRing C] [Algebra R' C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
    Function.Injective (θ C J) ∧
    (∀ x : F.Points C J,
      (∀ j, x.val j ∈ J) ↔
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (θ C J x).1 =
          (L.one (Spec.map (CommRingCat.ofHom
            ((Ideal.Quotient.mk J).comp ((algebraMap R' C).comp φ))))).1) ∧
    (∀ P : SchemeHomOver (paBase φ C) f,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 =
          (L.one (Spec.map (CommRingCat.ofHom
            ((Ideal.Quotient.mk J).comp ((algebraMap R' C).comp φ))))).1 →
        P ∈ Set.range (θ C J)) ∧
    (∀ x y : F.Points C J, θ C J (x + y) = L.mul (paBase φ C) (θ C J x) (θ C J y)) ∧
    (∀ (C' : Type) [CommRing C'] [Algebra R' C'] (J' : Ideal C') [IsAdicComplete J' C'], IsNilpotent J' →
      ∀ (φ : C →ₐ[R'] C') (x : F.Points C J) (x' : F.Points C' J'),
        (∀ j, x'.val j = φ (x.val j)) → (θ C' J' x').1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (θ C J x).1)

variable {θ}

theorem apply_val_eq_of_val_eq (H : IsKernelOfReductionData φ L F θ) (C : Type) [CommRing C] [Algebra R' C]
    (J₁ J₂ : Ideal C) [IsAdicComplete J₁ C] [IsAdicComplete J₂ C] (h₁ : IsNilpotent J₁) (h₂ : IsNilpotent J₂)
    (x₁ : F.Points C J₁) (x₂ : F.Points C J₂) (hx : x₁.val = x₂.val) : (θ C J₁ x₁).1 = (θ C J₂ x₂).1 := by
  obtain ⟨-, -, -, -, hnat⟩ := H C J₂ h₂
  have h := hnat C J₁ h₁ (AlgHom.id R' C) x₂ x₁ (fun j => by rw [hx]; rfl)
  rw [h]
  show Spec.map (CommRingCat.ofHom (RingHom.id C)) ≫ _ = _
  rw [CommRingCat.ofHom_id]
  show Spec.map (𝟙 (CommRingCat.of C)) ≫ _ = _
  rw [Spec.map_id, Category.id_comp]

def tuplePoint {C : Type} [CommRing C] (s : Fin n → C) : F.Points C (Ideal.span (Set.range s)) :=
  ⟨s, fun i => Ideal.le_radical (Ideal.subset_span ⟨i, rfl⟩)⟩

open Classical in

def eta (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L' : RelativeGroupLaw R' f')
    (θ : ∀ (C : Type) [CommRing C] [Algebra R' C] (J : Ideal C) [IsAdicComplete J C],
      F.Points C J → SchemeHomOver (paBase φ C) f) :
    RelativeGroupLaw.FormalCoordinates f' n :=
  fun C _ _ s =>
    if h : ∀ i, IsNilpotent (s i) then
      up φ g hg (@θ C _ _ (Ideal.span (Set.range s))
        (isAdicComplete_of_isNilpotent _ (isNilpotent_span_range s h)) (tuplePoint s))
    else L'.one _

theorem eta_of_isNilpotent {C : Type} [CommRing C] [Algebra R' C] (s : Fin n → C) (h : ∀ i, IsNilpotent (s i)) :
    eta φ g hg L' θ C s =
      up φ g hg (@θ C _ _ (Ideal.span (Set.range s))
        (isAdicComplete_of_isNilpotent _ (isNilpotent_span_range s h)) (tuplePoint s)) := by
  unfold eta
  rw [dif_pos h]

theorem eta_val_comp (H : IsKernelOfReductionData φ L F θ) {C : Type} [CommRing C] [Algebra R' C]
    (J : Ideal C) [IsAdicComplete J C] (hJ : IsNilpotent J) (s : Fin n → C) (hs : ∀ i, s i ∈ J) :
    (eta φ g hg L' θ C s).1 ≫ g = (θ C J ⟨s, fun i => Ideal.le_radical (hs i)⟩).1 := by
  have h : ∀ i, IsNilpotent (s i) := fun i => isNilpotent_of_mem hJ (hs i)
  rw [eta_of_isNilpotent φ s h, up_val_comp]
  exact @apply_val_eq_of_val_eq R R' _ _ φ A f L n F θ H C _ _ _ J
    (isAdicComplete_of_isNilpotent _ (isNilpotent_span_range s h)) _ (isNilpotent_span_range s h) hJ _ _ rfl

theorem isFormalCoordinates_eta (H : IsKernelOfReductionData φ L F θ) (hmul : IsMulCompat φ g hg L L') :
    L'.IsFormalCoordinates F (eta φ g hg L' θ) := by
  refine ⟨?_, ?_⟩
  ·
    intro C _ _ C' _ _ ψ s hs
    have hs' : ∀ i, IsNilpotent ((ψ ∘ s) i) := fun i => (hs i).map ψ
    haveI i1 := isAdicComplete_of_isNilpotent _ (isNilpotent_span_range s hs)
    haveI i2 := isAdicComplete_of_isNilpotent _ (isNilpotent_span_range _ hs')
    apply ext_of_comp_eq φ g hg
    rw [schemeHomOverComp_coe, Category.assoc,
      eta_val_comp φ H _ (isNilpotent_span_range s hs) s (fun i => Ideal.subset_span ⟨i, rfl⟩),
      eta_val_comp φ H _ (isNilpotent_span_range _ hs') (ψ ∘ s) (fun i => Ideal.subset_span ⟨i, rfl⟩)]
    obtain ⟨-, -, -, -, hnat⟩ := H C _ (isNilpotent_span_range s hs)
    exact hnat C' _ (isNilpotent_span_range _ hs') ψ _ _ (fun j => rfl)
  · intro C _ _ J k hJ
    have hJn : IsNilpotent J := ⟨k + 1, hJ⟩
    haveI := isAdicComplete_of_isNilpotent J hJn
    obtain ⟨hinj, ha, honto, hadd, -⟩ := H C J hJn
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      intro s hs
      rw [isInfinitesimal_iff_val]
      apply hg.hom_ext
      · rw [Category.assoc, eta_val_comp φ H J hJn s hs, (ha _).1 hs, one_val_comp φ g hg hmul]
        exact one_val_congr L (quotBase_eq φ C J)
      · rw [Category.assoc, (eta φ g hg L' θ C s).2, (L'.one (Scheme.specOver (𝒪 := R') (C ⧸ J))).2,
          specMap_mk_comp_specOver]
    ·
      intro s t hs ht hst
      have h := congrArg (fun P : SchemeHomOver _ f' => P.1 ≫ g) hst
      simp only [eta_val_comp φ H J hJn s hs, eta_val_comp φ H J hJn t ht] at h
      exact congrArg MvFormalGroup.Points.val (hinj (Subtype.ext h))
    ·
      intro P hP
      have hPval := (isInfinitesimal_iff_val (L := L') J P).1 hP
      have hd : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (down φ g hg P).1 =
          (L.one (Spec.map (CommRingCat.ofHom
            ((Ideal.Quotient.mk J).comp ((algebraMap R' C).comp φ))))).1 := by
        rw [down_val, ← Category.assoc, hPval, one_val_comp φ g hg hmul]
        exact one_val_congr L (quotBase_eq φ C J).symm
      obtain ⟨x, hx⟩ := honto (down φ g hg P) hd
      have hxJ : ∀ j, x.val j ∈ J := (ha x).2 (by rw [hx]; exact hd)
      refine ⟨x.val, hxJ, ?_⟩
      apply ext_of_comp_eq φ g hg
      rw [eta_val_comp φ H J hJn x.val hxJ, ← down_val φ g hg P, ← hx]
    ·
      intro s t hs ht
      have hst : ∀ i, F.nilMul k s t i ∈ J :=
        fun i => nilEval_mem J k _ (F.constantCoeff_eq_zero i) _ (by rintro (j | j); exacts [hs j, ht j])
      apply ext_of_comp_eq φ g hg
      have hm := hmul (Scheme.specOver (𝒪 := R') C) (eta φ g hg L' θ C s) (eta φ g hg L' θ C t)
      rw [eta_val_comp φ H J hJn _ hst, hm]
      have hpt : (⟨F.nilMul k s t, fun i => Ideal.le_radical (hst i)⟩ : F.Points C J) =
          ⟨s, fun i => Ideal.le_radical (hs i)⟩ + ⟨t, fun i => Ideal.le_radical (ht i)⟩ := by
        apply MvFormalGroup.Points.ext
        funext i
        rw [MvFormalGroup.Points.val_add]
        exact MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J k hJ _ _
          (by rintro (j | j); exacts [hs j, ht j])
      rw [hpt, hadd]
      apply mul_val_congr
      · exact (specOver_comp φ C).symm
      · exact (eta_val_comp φ H J hJn s hs).symm
      · exact (eta_val_comp φ H J hJn t ht).symm

theorem isFormalGroupAlong (H : IsKernelOfReductionData φ L F θ) (hmul : IsMulCompat φ g hg L L') :
    L'.IsFormalGroupAlong F :=
  ⟨eta φ g hg L' θ, isFormalCoordinates_eta φ H hmul⟩

end Bridge

end PABridge
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_isFormalModuleOf.PABridge"

namespace D2aFaceExists

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem subsingleton_mvPowerSeries {σ : Type} (R : Type) [CommRing R] [Subsingleton R] :
    Subsingleton (MvPowerSeries σ R) :=
  ⟨fun _ _ => MvPowerSeries.ext fun _ => Subsingleton.elim _ _⟩

theorem point_ext_of_subsingleton {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    {C : Type} [CommRing C] [Subsingleton C] {t : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of S)}
    (P Q : SchemeHomOver t f) : P = Q := by
  haveI : IsEmpty ↥(Spec (CommRingCat.of C)) := inferInstanceAs (IsEmpty (PrimeSpectrum C))
  exact Subtype.ext (AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _)

def trivialODModule (q : ℕ) [Fact q.Prime] (R : Type) [CommRing R] [Subsingleton R] : FormalODModule q R :=
  haveI := subsingleton_mvPowerSeries (σ := Fin 2) R
  { F := MvFormalGroup.addMv 2 R
    isComm := inferInstance
    act _ := Series.id R
    varpi := Series.id R
    isLawHom_act _ := IsLawHom.id _
    isLawHom_varpi := IsLawHom.id _
    act_one := rfl
    act_mul _ _ := Subsingleton.elim _ _
    act_add _ _ := Subsingleton.elim _ _
    varpi_comp_varpi := Subsingleton.elim _ _
    varpi_comp_act _ := Subsingleton.elim _ _ }

theorem exists_isFormalModuleOf_of_subsingleton {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ}
    [Fact q.Prime] (coord : ↥Λ → Zp2 q × Zp2 q) (R : Type) [CommRing R] [Subsingleton R]
    (E : FakeEllipticCurve Λ N R) : ∃ X : FormalODModule q R, E.IsFormalModuleOf coord X := by
  refine ⟨trivialODModule q R, fun B' _ _ _ => E.L.one _, ⟨?_, ?_⟩, ?_⟩
  · intro B' _ _ B'' _ _ φ s _
    haveI : Subsingleton B'' := Module.subsingleton R B''
    exact point_ext_of_subsingleton _ _
  · intro B' _ _ J n _
    haveI : Subsingleton B' := Module.subsingleton R B'
    refine ⟨fun s _ => ?_, fun s t _ _ _ => funext fun i => Subsingleton.elim _ _, fun P _ => ?_,
      fun s t _ _ => point_ext_of_subsingleton _ _⟩
    · haveI : Subsingleton (B' ⧸ J) := Module.subsingleton B' (B' ⧸ J)
      exact point_ext_of_subsingleton _ _
    · exact ⟨fun _ => 0, fun _ => J.zero_mem, point_ext_of_subsingleton _ _⟩
  · intro B' _ _ J n _ m s _
    haveI : Subsingleton B' := Module.subsingleton R B'
    exact point_ext_of_subsingleton _ _

theorem exists_isFormalModuleOf_local {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    {B : Type} [CommRing B] (E : FakeEllipticCurve Λ N B)
    (R : Type) [CommRing R] [Algebra B R] (hqR : IsNilpotent ((q : ℕ) : R))
    {g : ℕ} (F : MvFormalGroup g R) (hcomm : F.IsComm)
    (θ : ∀ (C : Type) [CommRing C] [Algebra R C] (J : Ideal C) [IsAdicComplete J C],
      F.Points C J → SchemeHomOver (PABridge.paBase (algebraMap B R) C) E.f)
    (H : PABridge.IsKernelOfReductionData (algebraMap B R) E.L F θ)
    (E' : FakeEllipticCurve Λ N R) (hE' : FakeEllipticCurve.IsPullback (algebraMap B R) E E') :
    ∃ X : FormalODModule q R, E'.IsFormalModuleOf coord X := by
  obtain ⟨g', hg', hmul, -, -⟩ := hE'

  have hη : E'.L.IsFormalCoordinates F (PABridge.eta (algebraMap B R) g' hg' E'.L θ) :=
    PABridge.isFormalCoordinates_eta (algebraMap B R) (hg := hg') (θ := θ) H @hmul
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact exists_isFormalModuleOf_of_subsingleton coord R E'
  ·
    obtain rfl : g = 2 :=
      CerednikDrinfeld.QM.FakeEllipticCurve.eq_two_of_isFormalGroupAlong R E' F ⟨_, hη⟩

    obtain ⟨X, -, hX⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_isFormalCoordinates coord hcoord R hqR E'
        F hcomm _ hη
    exact ⟨X, _, hX⟩

end D2aFaceExists
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_isFormalModuleOf.PABridge"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_isFormalModuleOf.PABridge"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal"

open scoped Quaternion TensorProduct NumberField

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧
      ∀ c ∈ s, ∀ E' : FakeEllipticCurve Λ N (Localization.Away c),
        FakeEllipticCurve.IsPullback (algebraMap B (Localization.Away c)) E E' →
        ∃ X : FormalODModule q (Localization.Away c), E'.IsFormalModuleOf coord X := by
  classical

  obtain ⟨n, a, hspan, hloc⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth E.L E.comm E.bundle.smooth
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspan
  · intro c hc E' hE'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨g, F, θ, hcomm, H, -, -⟩ := hloc i (Localization.Away (a i))
    have hqR : IsNilpotent ((q : ℕ) : Localization.Away (a i)) := by
      simpa only [map_natCast] using hq.map (algebraMap B (Localization.Away (a i)))
    exact D2aFaceExists.exists_isFormalModuleOf_local coord hcoord E (Localization.Away (a i)) hqR F hcomm θ H E' hE'

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_isFormalModuleOf
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_isFormalModuleOf (solution)
