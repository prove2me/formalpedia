-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.presentationLabel_unique_and_leg_eq_of_ptR_eq_pr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/5bad3347-56b9-504f-91f9-5513191c4597

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_eq_of_isNormLevelTransport_of_isNormLevelTransport
import Theorems.Thm_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwistVia_refl
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_presentationLabel_unique_and_leg_eq_of_ptR_eq_pr
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

namespace C1Aux

open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem schemeHomOverComp_pushPt (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T T' : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S)) (τ : T' ⟶ T) (hτ : τ ≫ t = t')
    (P : SchemeHomOver t E.f) :
    schemeHomOverComp τ hτ (pushPt (E.act x) (E.act_over x) P) = pushPt (E.act x) (E.act_over x) (schemeHomOverComp τ hτ P) := by
  apply Subtype.ext
  simp only [mapPt_coe, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]

theorem nsmulPt_natural (E : FakeEllipticCurve Λ N S) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T' ⟶ Spec (CommRingCat.of S)) (τ : T' ⟶ T) (hτ : τ ≫ t = t') (m : ℕ) (P : SchemeHomOver t E.f) :
    schemeHomOverComp τ hτ (nsmulPt E.L t m P) = nsmulPt E.L t' m (schemeHomOverComp τ hτ P) := by
  induction m with
  | zero => exact E.L.one_natural t t' τ hτ
  | succ m ih =>
    show schemeHomOverComp τ hτ (E.L.mul t (nsmulPt E.L t m P) P) = E.L.mul t' (nsmulPt E.L t' m (schemeHomOverComp τ hτ P)) _
    rw [E.L.mul_natural, ih]

theorem pushPt_act_one (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_hom x t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  have h' : pushPt (E.act x) (E.act_over x) (E.L.one t) * pushPt (E.act x) (E.act_over x) (E.L.one t) =
      pushPt (E.act x) (E.act_over x) (E.L.one t) := h.symm
  exact mul_eq_left.mp h'

theorem pushPt_act_nsmulPt (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (m : ℕ) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L t m P) = nsmulPt E.L t m (pushPt (E.act x) (E.act_over x) P) := by
  induction m with
  | zero => exact pushPt_act_one E x t
  | succ m ih =>
    show pushPt (E.act x) (E.act_over x) (E.L.mul t (nsmulPt E.L t m P) P) = E.L.mul t (nsmulPt E.L t m _) _
    rw [E.act_hom, ih]

theorem pushPt_pushPt (hΛo : QuaternionAlgebra.IsOrder Λ) (E : FakeEllipticCurve Λ N S) (x y : ↥Λ) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (pushPt (E.act y) (E.act_over y) P) =
      pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hΛo.mul_mem x.2 y.2⟩) (E.act_over _) P := by
  apply Subtype.ext
  simp only [mapPt_coe, E.act_mul x y (hΛo.mul_mem x.2 y.2), Category.assoc]

theorem pushPt_act_zero (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act 0) (E.act_over 0) P = E.L.one t := by
  letI := E.L.pointGroup t
  have h : E.L.mul t (pushPt (E.act 0) (E.act_over 0) P) (pushPt (E.act 0) (E.act_over 0) P) = pushPt (E.act 0) (E.act_over 0) P := by
    rw [← E.act_add, add_zero]
  have h' : pushPt (E.act 0) (E.act_over 0) P * pushPt (E.act 0) (E.act_over 0) P = pushPt (E.act 0) (E.act_over 0) P := h
  exact mul_eq_left.mp h'

theorem pushPt_act_natSmul (E : FakeEllipticCurve Λ N S) (z : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f) (m : ℕ) :
    pushPt (E.act (m • z)) (E.act_over (m • z)) P = nsmulPt E.L t m (pushPt (E.act z) (E.act_over z) P) := by
  induction m with
  | zero => rw [zero_smul]; exact pushPt_act_zero E t P
  | succ m ih =>
    rw [succ_nsmul, E.act_add, ih]
    rfl

theorem pushPt_act_eq_of_sub_eq_smul (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f) (m : ℕ) (hP : nsmulPt E.L t m P = E.L.one t) (x y : ↥Λ)
    (hxy : ∃ z : ↥Λ, (x : ℍ[ℚ, a, b]) - (y : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b])) :
    pushPt (E.act x) (E.act_over x) P = pushPt (E.act y) (E.act_over y) P := by
  letI := E.L.pointGroup t
  obtain ⟨z, hz⟩ := hxy
  have hxz : x = y + (m • z) := by
    apply Subtype.ext
    show (x : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b]) + ((m • z : ↥Λ) : ℍ[ℚ, a, b])
    rw [show ((m • z : ↥Λ) : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b]) from by simp [Nat.cast_smul_eq_nsmul], ← hz, add_sub_cancel]
  rw [hxz, E.act_add, pushPt_act_natSmul, ← pushPt_act_nsmulPt, hP, pushPt_act_one]
  exact mul_one _

theorem exists_geomPoint [Nontrivial S] : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k), Nonempty (S →+* k) := by
  obtain ⟨x⟩ : Nonempty ↥(Spec (CommRingCat.of S)) := inferInstance
  exact ⟨AlgebraicClosure x.asIdeal.ResidueField, inferInstance, inferInstance,
    ⟨(algebraMap x.asIdeal.ResidueField (AlgebraicClosure x.asIdeal.ResidueField)).comp (algebraMap S x.asIdeal.ResidueField)⟩⟩

theorem exists_sub_eq_smul_of_pushPt_act_eq [Nontrivial S] (E : FakeEllipticCurve Λ N S) {m : ℕ} (P : E.FullLevel m)
    (x y : ↥Λ) (h : pushPt (E.act x) (E.act_over x) P.P = pushPt (E.act y) (E.act_over y) P.P) :
    ∃ z : ↥Λ, (x : ℍ[ℚ, a, b]) - (y : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b]) := by
  obtain ⟨k, _, _, ⟨sk⟩⟩ := exists_geomPoint (S := S)
  letI := E.L.pointGroup (geomPoint k sk)
  have hsec : ∀ w : ↥Λ, sectionAt (pushPt (E.act w) (E.act_over w) P.P) k sk =
      pushPt (E.act w) (E.act_over w) (sectionAt P.P k sk) := fun w =>
    schemeHomOverComp_pushPt E w _ _ _ _ P.P
  have hxy : pushPt (E.act x) (E.act_over x) (sectionAt P.P k sk) = pushPt (E.act y) (E.act_over y) (sectionAt P.P k sk) := by
    rw [← hsec, ← hsec, h]
  have hw : pushPt (E.act (x - y)) (E.act_over (x - y)) (sectionAt P.P k sk) = E.L.one (geomPoint k sk) := by
    have h1 : pushPt (E.act x) (E.act_over x) (sectionAt P.P k sk) =
        E.L.mul _ (pushPt (E.act (x - y)) (E.act_over (x - y)) (sectionAt P.P k sk)) (pushPt (E.act y) (E.act_over y) (sectionAt P.P k sk)) := by
      rw [← E.act_add, sub_add_cancel]
    rw [hxy] at h1
    have h2 : pushPt (E.act (x - y)) (E.act_over (x - y)) (sectionAt P.P k sk) * pushPt (E.act y) (E.act_over y) (sectionAt P.P k sk) =
        pushPt (E.act y) (E.act_over y) (sectionAt P.P k sk) := h1.symm
    exact mul_eq_right.mp h2
  obtain ⟨z, hz⟩ := (P.annihilator k sk (x - y)).1 hw
  exact ⟨z, by rw [← hz, Submodule.coe_sub]⟩

end C1Aux

theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

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

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (p : M ⟶ 𝒳) (hp : p ≫ f = fM) (hρp : ∀ h : G, (ρ h).hom ≫ p = p)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ 𝒳) (hd₀f : ∀ ℓ, d₀ ℓ ≫ f = g ℓ) (hd₁f : ∀ ℓ, d₁ ℓ ≫ f = g ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt S s d).1)

    (ar arbar : 𝒳 ⟶ 𝒳) (harf : ar ≫ f = f) (harbarf : arbar ≫ f = f)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt S s E).1 ≫ ar = (pt S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient rbar E E' → (pt S s E).1 ≫ arbar = (pt S s E').1)

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)

    (wbar : (ℍ[ℚ, a₁, b₁])ˣ) (hwbar : nrd (wbar : ℍ[ℚ, a₁, b₁]) = ((rbar : ℕ) : ℚ) ∧ ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt → wbar * x * wbar⁻¹ ∈ Γt)

    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (e e' : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f) (deg : ↥Γt → ℕ)

    (hX₀ : X₀.HasHeight 4) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (hE1 :
      (∀ γ : ↥Γt, FakeEllipticCurve.IsIsogenyPair (r ^ deg γ) A₀ A₀ (e γ) (e' γ) ∧ FakeEllipticCurve.PreservesLevel A₀ A₀ (e γ) (he γ)))
    (hE1mul :
      (∀ γ γ' : ↥Γt, ∃ i j : ℕ,
          e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    (hE1sc :
      (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
          ∃ i : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c * ((r ^ i : ℕ) : ℤ) : ℤ) : ℚ), hΛℤ _⟩))

    (hE1' :
      (∀ (γ : ↥Γt), (∃ (i c : ℕ), 0 < c ∧ e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c : ℤ) : ℚ), hΛℤ _⟩) →
          ∃ c : ℚ, ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])))

    (hE2 :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, ∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (hE3 :
      (∀ P₀ : A₀.FullLevel n, ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b]))))

    (hE4 :
      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k]
          (A : FakeEllipticCurve Λ N k) (gA : A.A ⟶ A₀.A),
          FakeEllipticCurve.IsPullbackVia (algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k) A₀ A gA →
          (∀ (φ ψ : A.A ⟶ A.A) (d : ℕ) (hφ : φ ≫ A.f = A.f),
              FakeEllipticCurve.IsIsogenyPair (r ^ d) A A φ ψ → FakeEllipticCurve.PreservesLevel A A φ hφ →
              ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ A.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ gA = gA ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)))

    (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
          (hR₂r : ∀ x : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (x : ℍ[ℚ, a₁, b₁]) ∈ R₂)
          (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ x, ê x ≫ A₀.f = A₀.f)

        (hE5a : ∀ x : ↥R₂,
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
              mapPt (ê x) (hê x) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê x) (hê x) P) (mapPt (ê x) (hê x) Q)) ∧
          (∀ m : ↥Λ, A₀.act m ≫ ê x = ê x ≫ A₀.act m) ∧
          FakeEllipticCurve.PreservesLevel A₀ A₀ (ê x) (hê x))

        (hE5b1 : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A)
        (hE5b2 : ∀ (x y : ↥R₂) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
            ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê x)
        (hE5b3 : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)

        (hE5c : ∀ (x y : ↥R₂) (nx : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (x : ℍ[ℚ, a₁, b₁]) → nrd (x : ℍ[ℚ, a₁, b₁]) = (nx : ℚ) →
            ê y ≫ ê x = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩)

        (hE5d : ∀ (γ : ↥Γt) (x : ↥R₂) (k : ℕ),
            (x : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
            ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê x ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

        (hE5e : ∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
          ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
            (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                  J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                  θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                    mapPt (e γ) (he γ) (θ₀ B' s)) ∧
              E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧
            (∀ x : ↥R₂, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kx : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                  J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                  θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                    mapPt (ê x) (hê x) (θ₀ B' s)) ∧
              E₀ ε = ((r : K₀) ^ kx) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (x : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (MD : ModuliPackage.{0, 0} r Onr) (hMD : MD.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → MD.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = MD.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : MD.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  MD.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

      (eD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 MD).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)

      (hnatD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 MD).obj B), eD B' hB' ((ModuliPackage.G 𝒪 MD).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (eD B hB x))

      (hbijD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (eD B hB))

      (hfstD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 MD).obj B), (eD B hB x).1 = x.ψ)

      (hGLD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (eD B hB x) (eD B hB x'))

      (hPiD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → eD B hB x' = (frobTwist Onr Fr 1 (eD B hB x).1, (eD B hB x).2))

      (hPiexD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 MD).obj B), ∃ x' : (ModuliPackage.G 𝒪 MD).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x')

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (P₀ : A₀.FullLevel n)

    (A₀w : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
    (kw : ℕ) (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f) (bw' : A₀.A ⟶ A₀w.A) (habw : (aw ≫ bw) ≫ A₀.f = A₀.f)
    (hALw : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw')
    (hBSw : FakeEllipticCurve.IsIsogenyPair (r ^ kw) A₀w A₀ bw bw') (hBSwlev : FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw)
    (hJOINTw :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧

          (∃ (εw : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (k_w : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ v : Fin 2 → B', (∀ i, v i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εw : MvFormalGroup.End X₀.F).toPowerSeries i) v) =
                  mapPt (aw ≫ bw) habw (θ₀ B' v)) ∧
              E₀ εw = ((r : K₀) ^ k_w) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((wbar : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))))

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 MD B)

    (hΞleg :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ))

    (hΞnat :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ))

    (hΞiso :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x'))

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (g₀ : Matrix.GeneralLinearGroup (Fin 2) K₀)

      (heqΓ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (E : FakeEllipticCurve Λ N B) (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E) (γ : ↥Γt),
          FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ (e γ) ρ ρ' →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (γ : (ℍ[ℚ, a₁, b₁])ˣ) * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨E, ρ'⟩))

      (heqW : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hrbarB : IsUnit ((rbar : ℕ) : B))
          (E Ef : FakeEllipticCurve Λ N B)
          (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f) (q' : Ef.A ⟶ E.A) (hq' : q' ≫ E.f = Ef.f),
          FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar E Ef q hq q' hq' →
          ∀ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef),
          (∃ (qb : ρ.Eb.A ⟶ ρf.Eb.A) (_ : qb ≫ ρf.gb = ρ.gb ≫ q) (_ : qb ≫ ρf.Eb.f = ρ.Eb.f)
            (uA : ρf.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (_ : uA ≫ ρ.gA = ρf.gA)
            (ewb : ρ.Ab.A ⟶ ρ.Ab.A) (_ : ewb ≫ ρ.gA = ρ.gA ≫ (aw ≫ bw)) (_ : ewb ≫ ρ.Ab.f = ρ.Ab.f)
            (i j : ℕ),
            qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ewb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) wbar * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨Ef, ρf⟩))

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hCπ : IsNilpotent (algebraMap 𝒪 C π)) (χC : Onr →ₐ[𝒪] C)
    (PR : CerednikDrinfeld.FormalOmega.AlgFunctor C)
    (ptR : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (ψS : Onr →ₐ[𝒪] S) (_ : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S), FakeEllipticCurve.Rigidification r π A₀ ψS u.1 →
          PR.obj S)

    (hR2 : (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp χC)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            PR.map φ (ptR S ψS hψS u ρ) = ptR S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ'))

    (hR3s : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (z : PR.obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), ptR S ψS hψS u ρ = z))
    (hR3i : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ' →
            ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
              ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

    (hR1 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1)
          (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
          (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ'))
    (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Nontrivial S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (hc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (x : PR.obj S) (g : G) (j : Fin 2)
    :
      (∃ (hS : IsNilpotent (algebraMap 𝒪 S π)) (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
            ptR S ψS hψS u ρ = x ∧
            (∃ Pn : u.1.FullLevel n, FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ Pn ∧
              u.2.P = pushPt (u.1.act (χ g)) (u.1.act_over (χ g)) Pn.P) ∧
            (Ξ S ψS hS ⟨u.1, ρ⟩).ψ = frobTwist Onr Fr (-(j : ℤ)) ψS) →
        (∀ (g' : G) (j' : Fin 2),
          (∃ (hS : IsNilpotent (algebraMap 𝒪 S π)) (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
            ptR S ψS hψS u ρ = x ∧
            (∃ Pn : u.1.FullLevel n, FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ Pn ∧
              u.2.P = pushPt (u.1.act (χ g')) (u.1.act_over (χ g')) Pn.P) ∧
            (Ξ S ψS hS ⟨u.1, ρ⟩).ψ = frobTwist Onr Fr (-(j' : ℤ)) ψS) → g' = g ∧ j' = j) ∧
        (∀ (hS : IsNilpotent (algebraMap 𝒪 S π)) (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (u' : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          ptR S ψS hψS u' ρ' = x → (Ξ S ψS hS ⟨u'.1, ρ'⟩).ψ = frobTwist Onr Fr (-(j : ℤ)) ψS) := by
  classical
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.1

  obtain hC0u := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.eq_of_isNormLevelTransport_of_isNormLevelTransport
      (r := r) (rbar := rbar) (N := N) (hrr := hrr) (hrN := hrN) (hrbarN := hrbarN) (hN := hN) (𝒪 := 𝒪) (hdvr := hdvr) (π := π) (hπ := hπ) (hcomplete := hcomplete) (hres := hres) (hunr := hunr) (K₀ := K₀) (Onr := Onr) (Fr := Fr) (hOnr_complete := hOnr_complete) (hOnr_max := hOnr_max) (hOnr_alg := hOnr_alg) (hOnr_closed := hOnr_closed) (hFr := hFr) (vdet := vdet) (hvdet := hvdet) (a := a) (b := b) (hB := hB) (Λ := Λ) (hΛ := hΛ) (𝒳 := 𝒳) (f := f) (pt := pt) (h𝒳 := h𝒳) (n := n) (hn := hn) (hrn := hrn) (hrbarn := hrbarn) (hnN := hnN) (M := M) (fM := fM) (ptF := ptF) (hM := hM) (G := G) (ρ := ρ) (χ := χ) (hρ := hρ) (p := p) (hp := hp) (hρp := hρp) (hp_pt := hp_pt) (𝒴 := 𝒴) (g := ‹∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪)›) (ptT := ptT) (h𝒴 := h𝒴) (d₀ := d₀) (d₁ := d₁) (hd₀f := hd₀f) (hd₁f := hd₁f) (hd₀ := hd₀) (hd₁ := hd₁) (ar := ar) (arbar := arbar) (harf := harf) (harbarf := harbarf) (har := har) (harbar := harbar) (a₁ := a₁) (b₁ := b₁) (hdef := hdef) (Λ₁ := Λ₁) (R₁ := R₁) (hΛ₁ := hΛ₁) (hR₁ := hR₁) (hRΛ₁ := hRΛ₁) (n₁ := n₁) (hn₁ := hn₁) (hS₁ := hS₁) (ι₀ := ι₀) (hι₀ := hι₀) (v := v) (hv := hv) (Γt := Γt) (hΓt := hΓt) (s := s) (sf := sf) (hs := hs) (Γtℓ := Γtℓ) (hΓtℓ := hΓtℓ) (wbar := wbar) (hwbar := hwbar) (hΛℤ := hΛℤ) (coord := coord) (hcoord := hcoord) (A₀ := A₀) (X₀ := X₀) (θ₀ := θ₀) (e := e) (e' := e') (he := he) (deg := deg) (hX₀ := hX₀) (hA₀ := hA₀) (hE1 := hE1) (hE1mul := hE1mul) (hE1sc := hE1sc) (hE1' := hE1') (hE2 := hE2) (hE3 := hE3) (hE4 := hE4) (R₂ := R₂) (hR₂ := hR₂) (hR₂o := hR₂o) (hR₂r := hR₂r) (ê := ê) (hê := hê) (hE5a := hE5a) (hE5b1 := hE5b1) (hE5b2 := hE5b2) (hE5b3 := hE5b3) (hE5c := hE5c) (hE5d := hE5d) (hE5e := hE5e) (ι := ι) (Φ := Φ) (hΦ := hΦ) (hΦ4 := hΦ4) (MD := MD) (hMD := hMD) (η := η) (hη := hη) (E₀ := E₀) (hE₀ := hE₀) (eD := eD) (hnatD := hnatD) (hbijD := hbijD) (hfstD := hfstD) (hGLD := hGLD) (hPiD := hPiD) (hPiexD := hPiexD) (κ := κ) (hκ := hκ) (n₀ := n₀) (β₀ := β₀) (hβ₀ := hβ₀) (P₀ := P₀) (A₀w := A₀w) (aw := aw) (haw := haw) (aw' := aw') (haw' := haw') (kw := kw) (bw := bw) (hbw := hbw) (bw' := bw') (habw := habw) (hALw := hALw) (hBSw := hBSw) (hBSwlev := hBSwlev) (hJOINTw := hJOINTw) (Ξ := Ξ) (hΞleg := hΞleg) (hΞnat := hΞnat) (hΞiso := hΞiso) (hΞdef := hΞdef) (g₀ := g₀) (heqΓ := heqΓ) (heqW := heqW)
  have hUNN : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ₁ : Onr →ₐ[𝒪] B)
      (hB : IsNilpotent (algebraMap 𝒪 B π))
      (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ₁ E) (Pn Pn' : E.FullLevel n),
      FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn →
      FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn' → Pn.P = Pn'.P := by
    intro B _ _ _ ψ₁ hB E ϱ Pn Pn' h h'
    obtain ⟨ψ₂, hψ₂⟩ : ∃ ψ₂ : Onr →ₐ[𝒪] B, frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ₂ = ψ₁ := by
      refine ⟨frobTwist Onr Fr (Multiplicative.toAdd (vdet g₀)) ψ₁, ?_⟩
      apply AlgHom.ext; intro y
      simp only [frobTwist, AlgHom.comp_apply, AlgEquiv.coe_algHom]
      rw [← AlgEquiv.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, AlgEquiv.one_apply]
    subst hψ₂
    exact hC0u B hB ψ₂ E ϱ Pn Pn' h h'
  rintro ⟨hS₁, ψ₁, hψ₁, u₁, ρ₁, hpt₁, ⟨Pn₁, hN₁, hlev₁⟩, hleg₁⟩

  have hΞeq : ∀ (u' : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ₁ u'.1),
      ptR S ψ₁ hψ₁ u' ρ' = x → Ξ S ψ₁ hS₁ ⟨u'.1, ρ'⟩ = Ξ S ψ₁ hS₁ ⟨u₁.1, ρ₁⟩ := by
    intro u' ρ' h
    obtain ⟨i, hi, hW, ib, h1, h2, uA, h3, h4, i₁, j₁, hcr⟩ := hR3i S ψ₁ hψ₁ hc u' u₁ ρ' ρ₁ (h.trans hpt₁.symm)
    exact hΞiso S ψ₁ hS₁ ⟨u'.1, ρ'⟩ ⟨u₁.1, ρ₁⟩ i hi ⟨hW.1, hW.2.1, hW.2.2.1⟩ ⟨ib, h1, h2, uA, h3, h4, i₁, j₁, hcr⟩
  refine ⟨?_, ?_⟩
  swap
  · intro hS ψS hψS u' ρ' hpt'
    have e : ψ₁ = ψS := hψ₁.trans hψS.symm
    subst e
    have e2 : hS₁ = hS := rfl
    subst e2
    rw [hΞeq u' ρ' hpt']
    exact hleg₁
  · rintro g' j' ⟨hS', ψ', hψ', u', ρ', hpt', ⟨Pn', hN', hlev'⟩, hleg'⟩
    have e : ψ₁ = ψ' := hψ₁.trans hψ'.symm
    subst e
    have e2 : hS₁ = hS' := rfl
    subst e2
    refine ⟨?_, ?_⟩
    swap
    ·
      have hk : frobTwist Onr Fr (-(j' : ℤ)) ψ₁ = frobTwist Onr Fr (-(j : ℤ)) ψ₁ := by
        rw [← hleg', hΞeq u' ρ' hpt', hleg₁]
      have hz := CerednikDrinfeld.FormalOmega.eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial π Onr Fr hOnr_closed hFr
        S hS₁ ψ₁ _ _ hk
      apply Fin.ext
      omega
    ·
      obtain ⟨i, hi, hW, ib, h1, h2, uA, h3, h4, i₁, j₁, hcr⟩ := hR3i S ψ₁ hψ₁ hc u₁ u' ρ₁ ρ' (hpt₁.trans hpt'.symm)

      obtain ⟨y₀, hy₀⟩ := hρ.label_one
      obtain ⟨y₁, hy₁⟩ := hρ.label_mul g⁻¹ g
      obtain ⟨y₂, hy₂⟩ := hρ.label_mul g g⁻¹
      have hcd : ∃ y : ↥Λ, (χ g⁻¹ : ℍ[ℚ, a, b]) * (χ g : ℍ[ℚ, a, b]) - 1 = (n : ℚ) • (y : ℍ[ℚ, a, b]) := by
        refine ⟨y₀ - y₁, ?_⟩
        rw [inv_mul_cancel] at hy₁
        rw [Submodule.coe_sub, smul_sub, ← hy₀, ← hy₁]; abel
      have hdc : ∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) * (χ g⁻¹ : ℍ[ℚ, a, b]) - 1 = (n : ℚ) • (y : ℍ[ℚ, a, b]) := by
        refine ⟨y₀ - y₂, ?_⟩
        rw [mul_inv_cancel] at hy₂
        rw [Submodule.coe_sub, smul_sub, ← hy₀, ← hy₂]; abel
      obtain ⟨Q, hQ⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isTwistVia_refl hΛo u' (χ g⁻¹) (χ g) hcd hdc

      have hmapact : ∀ (z : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) u₁.1.f),
          mapPt i.hom hi (pushPt (u₁.1.act z) (u₁.1.act_over z) P) = pushPt (u'.1.act z) (u'.1.act_over z) (mapPt i.hom hi P) := by
        intro z P
        apply Subtype.ext
        simp only [mapPt_coe, Category.assoc, hW.2.1 z]
      have hmapone : mapPt i.hom hi (u₁.1.L.one (𝟙 _)) = u'.1.L.one (𝟙 _) := by
        letI := u'.1.L.pointGroup (𝟙 (Spec (CommRingCat.of S)))
        have h := hW.1 (𝟙 _) (u₁.1.L.one _) (u₁.1.L.one _)
        rw [u₁.1.L.one_mul] at h
        have h' : mapPt i.hom hi (u₁.1.L.one (𝟙 _)) * mapPt i.hom hi (u₁.1.L.one (𝟙 _)) = mapPt i.hom hi (u₁.1.L.one (𝟙 _)) := h.symm
        exact mul_eq_left.mp h'
      have hmapns : ∀ (m : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) u₁.1.f),
          mapPt i.hom hi (nsmulPt u₁.1.L (𝟙 _) m P) = nsmulPt u'.1.L (𝟙 _) m (mapPt i.hom hi P) := by
        intro m P
        induction m with
        | zero => exact hmapone
        | succ m ih =>
          show mapPt i.hom hi (u₁.1.L.mul _ (nsmulPt u₁.1.L _ m P) P) = u'.1.L.mul _ (nsmulPt u'.1.L _ m (mapPt i.hom hi P)) _
          rw [hW.1, ih]

      have htors : nsmulPt u'.1.L (𝟙 _) n (mapPt i.hom hi Pn₁.P) = u'.1.L.one (𝟙 _) := by
        rw [← hmapns, Pn₁.torsion, hmapone]
      have hQP : mapPt i.hom hi Pn₁.P = Q.P := by
        rw [← hQ.2.2.2]
        have hrefl : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) u'.1.f),
            mapPt (Iso.refl u'.1.A).hom (Category.id_comp u'.1.f) P = P := fun P =>
          Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
        rw [hrefl, ← hW.2.2.2, hlev₁, hmapact, C1Aux.pushPt_pushPt hΛo]
        symm
        have h1 : pushPt (u'.1.act ⟨(1 : ℍ[ℚ, a, b]), hΛo.one_mem⟩) (u'.1.act_over _) (mapPt i.hom hi Pn₁.P) = mapPt i.hom hi Pn₁.P := by
          apply Subtype.ext; simp only [mapPt_coe, u'.1.act_one hΛo.one_mem, Category.comp_id]
        exact (C1Aux.pushPt_act_eq_of_sub_eq_smul u'.1 _ _ n htors _ ⟨(1 : ℍ[ℚ, a, b]), hΛo.one_mem⟩ hcd).trans h1

      have hNQ : FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ' Q :=
        CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia
          (r := r) (rbar := rbar) (N := N) (hrr := hrr) (hrN := hrN) (𝒪 := 𝒪) (hdvr := hdvr) (π := π) (hπ := hπ) (hcomplete := hcomplete) (hres := hres) (hunr := hunr) (K₀ := K₀) (Onr := Onr) (Fr := Fr) (hOnr_complete := hOnr_complete) (hOnr_max := hOnr_max) (hOnr_alg := hOnr_alg) (hOnr_closed := hOnr_closed) (hFr := hFr) (a := a) (b := b) (hB := hB) (Λ := Λ) (hΛ := hΛ) (hΛℤ := hΛℤ) (coord := coord) (hcoord := hcoord) (A₀ := A₀) (X₀ := X₀) (hX₀ := hX₀) (θ₀ := θ₀) (hA₀ := hA₀) (ι := ι) (Φ := Φ) (hΦ := hΦ) (hΦ4 := hΦ4) (M := MD) (hM := hMD) (η := η) (hη := hη) (E₀ := E₀) (hE₀ := hE₀) (κ := κ) (hκ := hκ) (n₀ := n₀) (β₀ := β₀) (hβ₀ := hβ₀) (n := n) (P₀ := P₀) (hrn := hrn)
          S ψ₁ hS₁ u₁.1 u'.1 i hi ⟨hW.1, hW.2.1, hW.2.2.1⟩ ρ₁ ρ' ib h1 h2 uA h3 h4 i₁ j₁ hcr Pn₁ Q hQP hN₁
      have hQPn' : Q.P = Pn'.P := hUNN S ψ₁ hS₁ u'.1 ρ' Q Pn' hNQ hN'

      have hcmp : pushPt (u'.1.act (χ g)) (u'.1.act_over (χ g)) Pn'.P = pushPt (u'.1.act (χ g')) (u'.1.act_over (χ g')) Pn'.P := by
        rw [← hlev', ← hW.2.2.2, hlev₁, hmapact, hQP, hQPn']
      obtain ⟨z, hz⟩ := C1Aux.exists_sub_eq_smul_of_pushPt_act_eq u'.1 Pn' (χ g) (χ g') hcmp
      exact (hρ.label_injective g g' ⟨z, hz⟩).symm

end S_CerednikDrinfeld_QM_FakeEllipticCurve_presentationLabel_unique_and_leg_eq_of_ptR_eq_pr
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_presentationLabel_unique_and_leg_eq_of_ptR_eq_pr (solution)
