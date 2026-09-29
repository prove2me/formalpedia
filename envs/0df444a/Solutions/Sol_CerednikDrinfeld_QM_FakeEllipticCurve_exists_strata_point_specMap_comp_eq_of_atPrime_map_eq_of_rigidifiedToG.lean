-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_strata_point_specMap_comp_eq_of_atPrime_map_eq_of_rigidifiedToG
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/05a53e83-e4ea-506d-8d81-3a76ab79a3fb

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_strata_point_specMap_comp_eq_of_atPrime_map_eq_of_rigidifiedToG
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

open LT.LatticeTree (FullLattice)

namespace StratEq

open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

abbrev zΛ (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m : ℤ) : ↥Λ := ⟨((m : ℚ) : ℍ[ℚ, a, b]), hΛℤ m⟩

theorem coe_zΛ (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m : ℤ) :
    ((zΛ hΛℤ m : ↥Λ) : ℍ[ℚ, a, b]) = (m : ℍ[ℚ, a, b]) := by
  show ((m : ℚ) : ℍ[ℚ, a, b]) = (m : ℍ[ℚ, a, b])
  exact_mod_cast rfl

theorem zΛ_comm (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m : ℤ) (x : ℍ[ℚ, a, b]) :
    ((zΛ hΛℤ m : ↥Λ) : ℍ[ℚ, a, b]) * x = x * (zΛ hΛℤ m : ↥Λ) := by
  rw [coe_zΛ]; exact Int.cast_comm m x

theorem mul_zΛ_mem (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (x : ↥Λ) (m : ℤ) :
    (x : ℍ[ℚ, a, b]) * (zΛ hΛℤ m : ↥Λ) ∈ Λ := by
  rw [← zΛ_comm, coe_zΛ, ← zsmul_eq_mul]; exact Λ.smul_mem m x.2

theorem zΛ_mul_mem (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m : ℤ) (x : ↥Λ) :
    ((zΛ hΛℤ m : ↥Λ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [coe_zΛ, ← zsmul_eq_mul]; exact Λ.smul_mem m x.2

theorem zΛ_mul_zΛ_mem (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m m' : ℤ) :
    ((zΛ hΛℤ m : ↥Λ) : ℍ[ℚ, a, b]) * (zΛ hΛℤ m' : ↥Λ) ∈ Λ := zΛ_mul_mem hΛℤ m _

theorem act_comm_zΛ (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {S : Type} [CommRing S]
    (F : FakeEllipticCurve Λ N S) (x : ↥Λ) (m : ℤ) :
    F.act x ≫ F.act (zΛ hΛℤ m) = F.act (zΛ hΛℤ m) ≫ F.act x := by
  rw [← F.act_mul (zΛ hΛℤ m) x (zΛ_mul_mem hΛℤ m x), ← F.act_mul x (zΛ hΛℤ m) (mul_zΛ_mem hΛℤ x m)]
  congr 1; apply Subtype.ext; exact zΛ_comm hΛℤ m x

theorem act_zΛ_comp_act_zΛ (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {S : Type} [CommRing S]
    (F : FakeEllipticCurve Λ N S) (m m' : ℤ) :
    F.act (zΛ hΛℤ m) ≫ F.act (zΛ hΛℤ m') = F.act (zΛ hΛℤ (m' * m)) := by
  rw [← F.act_mul (zΛ hΛℤ m') (zΛ hΛℤ m) (zΛ_mul_zΛ_mem hΛℤ m' m)]
  congr 1; apply Subtype.ext
  show ((zΛ hΛℤ m' : ↥Λ) : ℍ[ℚ, a, b]) * (zΛ hΛℤ m : ↥Λ) = ((zΛ hΛℤ (m' * m) : ↥Λ) : ℍ[ℚ, a, b])
  rw [coe_zΛ, coe_zΛ, coe_zΛ]; push_cast; rfl

example (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (r j : ℕ) :
    (zΛ hΛℤ ((r ^ j : ℕ) : ℤ) : ↥Λ) = ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := rfl

section Pad

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

theorem mapPt_comp' {R : Type} [CommRing R] {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) (γ : A' ⟶ A'') (hγ : γ ≫ f'' = f') (hφγ : (φ ≫ γ) ≫ f'' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ γ) hφγ P = mapPt γ hγ (mapPt φ hφ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem isIsogenyPair_pad (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {S : Type} [CommRing S]
    {E₁ E₂ : FakeEllipticCurve Λ N S} {φ : E₁.A ⟶ E₂.A} {φ' : E₂.A ⟶ E₁.A} {d : ℕ}
    (h : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₁ E₂ φ φ') (j k : ℕ) :
    FakeEllipticCurve.IsIsogenyPair (r ^ (d + j + k)) E₁ E₂
      (φ ≫ E₂.act (zΛ hΛℤ ((r ^ j : ℕ) : ℤ))) (φ' ≫ E₁.act (zΛ hΛℤ ((r ^ k : ℕ) : ℤ))) := by
  obtain ⟨hφ, hφ', hmul, hmul', hact, hact', hdeg⟩ := h
  have hφc : (φ ≫ E₂.act (zΛ hΛℤ ((r ^ j : ℕ) : ℤ))) ≫ E₂.f = E₁.f := by rw [Category.assoc, E₂.act_over, hφ]
  have hφ'c : (φ' ≫ E₁.act (zΛ hΛℤ ((r ^ k : ℕ) : ℤ))) ≫ E₁.f = E₂.f := by rw [Category.assoc, E₁.act_over, hφ']
  refine ⟨hφc, hφ'c, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [mapPt_comp' φ hφ _ (E₂.act_over _) hφc, mapPt_comp' φ hφ _ (E₂.act_over _) hφc,
      mapPt_comp' φ hφ _ (E₂.act_over _) hφc, hmul]
    exact E₂.act_hom _ t _ _
  · intro T t P Q
    rw [mapPt_comp' φ' hφ' _ (E₁.act_over _) hφ'c, mapPt_comp' φ' hφ' _ (E₁.act_over _) hφ'c,
      mapPt_comp' φ' hφ' _ (E₁.act_over _) hφ'c, hmul']
    exact E₁.act_hom _ t _ _
  · intro x
    rw [← Category.assoc, hact, Category.assoc, Category.assoc, act_comm_zΛ]
  · intro x
    rw [← Category.assoc, hact', Category.assoc, Category.assoc, act_comm_zΛ]
  · intro hd'
    have hdm : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ ((r ^ d : ℕ) : ℤ)
    obtain ⟨h1, h2⟩ := hdeg hdm
    have e1 : (⟨((r ^ d : ℕ) : ℚ), hdm⟩ : ↥Λ) = zΛ hΛℤ ((r ^ d : ℕ) : ℤ) := Subtype.ext (by rw [coe_zΛ]; push_cast; rfl)
    have e2 : (⟨((r ^ (d + j + k) : ℕ) : ℚ), hd'⟩ : ↥Λ) = zΛ hΛℤ ((r ^ (d + j + k) : ℕ) : ℤ) :=
      Subtype.ext (by rw [coe_zΛ]; push_cast; rfl)
    have ekj : (((r ^ k : ℕ) : ℤ) * ((r ^ j : ℕ) : ℤ)) * ((r ^ d : ℕ) : ℤ) = ((r ^ (d + j + k) : ℕ) : ℤ) := by
      push_cast; ring
    have ejk : (((r ^ j : ℕ) : ℤ) * ((r ^ k : ℕ) : ℤ)) * ((r ^ d : ℕ) : ℤ) = ((r ^ (d + j + k) : ℕ) : ℤ) := by
      push_cast; ring
    rw [e1] at h1 h2
    constructor
    ·
      rw [Category.assoc, ← Category.assoc (E₂.act _) φ', hact', Category.assoc, ← Category.assoc φ φ', h1,
        act_zΛ_comp_act_zΛ, act_zΛ_comp_act_zΛ, e2, ekj]
    · rw [Category.assoc, ← Category.assoc (E₁.act _) φ, hact, Category.assoc, ← Category.assoc φ' φ, h2,
        act_zΛ_comp_act_zΛ, act_zΛ_comp_act_zΛ, e2, ejk]

def pad (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (j k : ℕ) (ρ : Rigidification r π A₀ ψ E) :
    Rigidification r π A₀ ψ E where
  Eb := ρ.Eb
  gb := ρ.gb
  isPullback_Eb := ρ.isPullback_Eb
  Ab := ρ.Ab
  gA := ρ.gA
  isPullback_Ab := ρ.isPullback_Ab
  d := ρ.d + j + k
  φ := ρ.φ ≫ ρ.Ab.act (zΛ hΛℤ ((r ^ j : ℕ) : ℤ))
  φ' := ρ.φ' ≫ ρ.Eb.act (zΛ hΛℤ ((r ^ k : ℕ) : ℤ))
  φ_over := by rw [Category.assoc, ρ.Ab.act_over, ρ.φ_over]
  isIsogenyPair := isIsogenyPair_pad hΛℤ ρ.isIsogenyPair j k
  preservesLevel := by
    intro T t P hP
    have := ρ.Ab.lev_stable (zΛ hΛℤ ((r ^ j : ℕ) : ℤ)) t _ (ρ.preservesLevel t P hP)
    rw [mapPt_comp' ρ.φ ρ.φ_over _ (ρ.Ab.act_over _)]
    exact this

@[scoped simp] theorem pad_d (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (j k : ℕ) (ρ : Rigidification r π A₀ ψ E) :
    (pad hΛℤ j k ρ).d = ρ.d + j + k := rfl
@[scoped simp] theorem pad_φ (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (j k : ℕ) (ρ : Rigidification r π A₀ ψ E) :
    (pad hΛℤ j k ρ).φ = ρ.φ ≫ ρ.Ab.act (zΛ hΛℤ ((r ^ j : ℕ) : ℤ)) := rfl

end Pad

section PadLemmas

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

theorem mapPt_refl {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (h : (Iso.refl A).hom ≫ f = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (Iso.refl A).hom h P = P :=
  Subtype.ext (Category.comp_id _)

theorem isoVia_refl {S : Type} [CommRing S] {n : ℕ} (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (h : (Iso.refl u.1.A).hom ≫ u.1.f = u.1.f) : FakeEllipticCurve.WithFullLevel.IsoVia u u (Iso.refl u.1.A) h := by
  refine ⟨fun t P Q => ?_, fun x => ?_, fun t P => ?_, ?_⟩
  · rw [mapPt_refl, mapPt_refl, mapPt_refl]
  · simp
  · rw [mapPt_refl]
  · rw [mapPt_refl]

theorem act_zΛ_pow_zero (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {S : Type} [CommRing S]
    (F : FakeEllipticCurve Λ N S) : F.act (zΛ hΛℤ ((r ^ 0 : ℕ) : ℤ)) = 𝟙 F.A := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ 1
  rw [← F.act_one h1]
  congr 1
  all_goals (apply Subtype.ext; rw [coe_zΛ]; push_cast)

theorem corr_pad (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (j k : ℕ) (ρ : Rigidification r π A₀ ψ E) :
    ∃ (ib : (pad hΛℤ j k ρ).Eb.A ⟶ ρ.Eb.A) (_ : ib ≫ ρ.gb = (pad hΛℤ j k ρ).gb ≫ (Iso.refl E.A).hom)
      (_ : ib ≫ ρ.Eb.f = (pad hΛℤ j k ρ).Eb.f)
      (uA : ρ.Ab.A ⟶ (pad hΛℤ j k ρ).Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) (pad hΛℤ j k ρ).Ab ρ.Ab uA)
      (_ : uA ≫ (pad hΛℤ j k ρ).gA = ρ.gA) (i₁ j₁ : ℕ),
      ib ≫ ρ.φ ≫ uA ≫ (pad hΛℤ j k ρ).Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        (pad hΛℤ j k ρ).φ ≫ (pad hΛℤ j k ρ).Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  refine ⟨𝟙 _, by simp [pad], by simp [pad], 𝟙 _, CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _, by simp [pad],
    j, 0, ?_⟩
  show 𝟙 _ ≫ ρ.φ ≫ 𝟙 _ ≫ ρ.Ab.act (zΛ hΛℤ ((r ^ j : ℕ) : ℤ)) =
    (ρ.φ ≫ ρ.Ab.act (zΛ hΛℤ ((r ^ j : ℕ) : ℤ))) ≫ ρ.Ab.act (zΛ hΛℤ ((r ^ 0 : ℕ) : ℤ))
  rw [Category.id_comp, Category.id_comp, act_zΛ_pow_zero, Category.comp_id]

theorem isPullbackVia_pad (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (j k : ℕ)
    {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {E' : FakeEllipticCurve Λ N B'} (g : E'.A ⟶ E.A) (hE' : FakeEllipticCurve.IsPullbackVia (f : B →+* B') E E' g)
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ (f.comp ψ) E')
    (h : Rigidification.IsPullbackVia f g hE' ρ ρ') :
    Rigidification.IsPullbackVia f g hE' (pad hΛℤ j k ρ) (pad hΛℤ j k ρ') := by
  obtain ⟨ub, uA, hEb, hgb, hAb, hgA, hd, hφ⟩ := h
  refine ⟨ub, uA, hEb, hgb, hAb, hgA, by simp [pad, hd], ?_⟩
  obtain ⟨_, _, hact, _⟩ := hAb
  show ub ≫ (ρ.φ ≫ ρ.Ab.act _) = (ρ'.φ ≫ ρ'.Ab.act _) ≫ uA
  rw [← Category.assoc, hφ, Category.assoc, Category.assoc, hact]

theorem IsPullbackVia.d_eq {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {E' : FakeEllipticCurve Λ N B'} (g : E'.A ⟶ E.A) (hE' : FakeEllipticCurve.IsPullbackVia (f : B →+* B') E E' g)
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ (f.comp ψ) E')
    (h : Rigidification.IsPullbackVia f g hE' ρ ρ') : ρ'.d = ρ.d := by
  obtain ⟨_, _, _, _, _, _, hd, _⟩ := h; exact hd

end PadLemmas

theorem hconn_local (S : Type) [CommRing S] [IsLocalRing S] (e : S) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  by_cases hu : IsUnit e
  · right
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    have h2 : 1 - e = 0 := (hu.mul_right_eq_zero).mp h1
    linear_combination -h2
  · by_cases hu' : IsUnit (1 - e)
    · left
      have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
      exact (hu'.mul_right_eq_zero).mp h1
    · exfalso
      have hm : e ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hu
      have hm' : 1 - e ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hu'
      have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
        have := Ideal.add_mem _ hm hm'; rwa [add_sub_cancel] at this
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

end StratEq
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_strata_point_specMap_comp_eq_of_atPrime_map_eq_of_rigidifiedToG.StratEq"

open StratEq in
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

    (μΛ : ↥Λ) (hμΛ : (μΛ : ℍ[ℚ, a, b]) * (μΛ : ℍ[ℚ, a, b]) = -(((r * rbar : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (starΛ : ↥Λ → ↥Λ) (hstarΛ : ∀ x : ↥Λ, (μΛ : ℍ[ℚ, a, b]) * (starΛ x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μΛ)
    (h2 : IsUnit ((2 : ℕ) : 𝒪))
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

      (hbdd : ∀ (M' M : FullLattice 𝒪 K₀), M'.1 ≤ M.1 → (∀ v ∈ M.1, algebraMap 𝒪 K₀ π • v ∈ M'.1) →
        ∃ Nγ : ℕ, ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsArtinianRing B]
          [IsAlgClosed (IsLocalRing.ResidueField B)] [Algebra 𝒪 B]
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (ModuliPackage.G 𝒪 MD).obj B),
          DeligneDatum.InEdgeChart π (eD B hB y).2 M' M →
            ∃ t : Rigidified r Φ B, t.IsAdmissible ι (y.ψ : Onr →+* B) ∧ η B (y.ψ : Onr →+* B) y.nilp t = y.pt ∧ t.n ≤ Nγ)

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

    (θ : (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
        PR.obj S → (Omega K₀ π).obj S))
    (hθnat : (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          (g : S →ₐ[C] S') (x : PR.obj S),
          θ S' (PR.map g x) = (Omega K₀ π).map (g.restrictScalars 𝒪) (θ S x)))
    (hθ : (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (hS : IsNilpotent (algebraMap 𝒪 S π))
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
          θ S (ptR S ψS hψS u ρ) = DeligneDatum.pullback π S (g₀⁻¹)⁻¹ (eD S hS (Ξ S ψS hS ⟨u.1, ρ⟩)).2))

    (toM : ∀ (S : Type) [CommRing S] [Algebra C S],
        PR.obj S → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

(hR0 : ∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S') (x : PR.obj S),
        (toM S' (PR.map φ x)).1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (toM S x).1)

(hR4 : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
        (toM S (ptR S ψS hψS u ρ)).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1)

(hsh : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
      (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i)

(het' : ∀ (S S₀ : Type) [CommRing S] [IsNoetherianRing S] [Algebra C S] [CommRing S₀] [Algebra C S₀] (p : S →ₐ[C] S₀),
        Function.Surjective p → RingHom.ker (p : S →+* S₀) ^ 2 = ⊥ →
        ∀ (x₀ : PR.obj S₀) (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
        Spec.map (CommRingCat.ofHom (p : S →+* S₀)) ≫ t.1 = (toM S₀ x₀).1 →
        ∃! x : PR.obj S, PR.map p x = x₀ ∧ toM S x = t)

(hred : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra C T]
        (xb : PR.obj (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))
        (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ t.1 =
          (toM _ xb).1 →
        ∃! x : PR.obj T,
          PR.map (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) x = xb ∧ toM T x = t)
    (Xs : ℕ → Scheme.{0}) (ξ : ∀ d, Xs d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hξ : ∀ d, LocallyOfFinitePresentation (ξ d)) (hunrξ : ∀ d, FormallyUnramified (ξ d))
    (pts : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T],
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) → PR.obj T)
    (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
            (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
            ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

(hs0 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            algebraMap C T (algebraMap 𝒪 C π) = 0)

(hs1 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            (toM T (pts d T x)).1 = x.1 ≫ ξ d)

(hs2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
            (x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T'))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            x'.1 = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ x.1 → pts d T' x' = PR.map φ (pts d T x))

(hx1 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
              (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
              pts d T (ptX d T ψT hψT u ρ hd h0) = ptR T ψT hψT u ρ)

(hx2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp χC)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
              (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
              (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
              (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
              (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
              FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                  Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1)

(hx3 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                ptX d T ψT hψT u ρ hd h0 = x)

(hx4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
              (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
              (hd : ρ.d = d) (hd' : ρ'.d = d),
              (ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 ↔
                ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                  ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                    ib ≫ ρ'.φ ≫ uA = ρ.φ))

(hs4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
            (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
            algebraMap C T (algebraMap 𝒪 C π) = 0 →
            ((∃ x, pts d T x = ptR T ψT hψT u ρ) ↔
              ∃ (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u.1), ρ'.d = d ∧ ptR T ψT hψT u ρ' = ptR T ψT hψT u ρ))

    (gπ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hgπ : (gπ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    :
      ∀ (A : Type) [CommRing A] [Algebra C A] [IsNoetherianRing A] [Algebra 𝒪 A] [IsScalarTower 𝒪 C A]
        (_ : algebraMap C A (algebraMap 𝒪 C π) = 0) (𝔭 : Ideal A) [𝔭.IsPrime]
        (L : Type) [CommRing L] [Algebra A L] [Algebra C L] [IsScalarTower C A L] [IsLocalization.AtPrime L 𝔭]
        (x x' : PR.obj A),
        PR.map (IsScalarTower.toAlgHom C A L) x = PR.map (IsScalarTower.toAlgHom C A L) x' →
        ∃ (d : ℕ)
          (y y' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C A))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
          pts d A y = x ∧ pts d A y' = x' ∧
          Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ y.1 = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ y'.1 := by
  classical
  intro A _ _ _ _ _ hπA 𝔭 _ L _ _ _ _ _ x x' hxx

  letI instOL : Algebra 𝒪 L := ((algebraMap C L).comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L 𝔭
  let φL : A →ₐ[C] L := IsScalarTower.toAlgHom C A L
  have hφL : (φL : A →+* L) = algebraMap A L := rfl
  let ψA : Onr →ₐ[𝒪] A := (IsScalarTower.toAlgHom 𝒪 C A).comp χC
  have hψL : (φL.restrictScalars 𝒪).comp ψA = (IsScalarTower.toAlgHom 𝒪 C L).comp χC := by
    ext y
    simp only [ψA, φL, AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom',
      ← IsScalarTower.algebraMap_apply C A L]

  obtain ⟨u, ρ, hx⟩ := hR3s A ψA rfl x
  obtain ⟨u', ρ', hx'⟩ := hR3s A ψA rfl x'

  obtain ⟨uL, g, hsq, hmul, hact, hlev, -, hPP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (φL : A →+* L) u
  have hg : FakeEllipticCurve.IsPullbackVia (φL : A →+* L) u.1 uL.1 g := ⟨hsq, hmul, hact, hlev⟩
  obtain ⟨ρL, hρL⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia
      𝒪 π Onr Λ A₀ A L (φL.restrictScalars 𝒪) ψA u.1 uL.1 g hg ρ
  obtain ⟨uL', g', hsq', hmul', hact', hlev', -, hPP'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (φL : A →+* L) u'
  have hg' : FakeEllipticCurve.IsPullbackVia (φL : A →+* L) u'.1 uL'.1 g' := ⟨hsq', hmul', hact', hlev'⟩
  obtain ⟨ρL', hρL'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia
      𝒪 π Onr Λ A₀ A L (φL.restrictScalars 𝒪) ψA u'.1 uL'.1 g' hg' ρ'

  have hLeq : ptR L ((φL.restrictScalars 𝒪).comp ψA) hψL uL ρL = ptR L ((φL.restrictScalars 𝒪).comp ψA) hψL uL' ρL' := by
    rw [← hR2 A L φL ψA rfl hψL u uL ρ ρL g hg hPP hρL, ← hR2 A L φL ψA rfl hψL u' uL' ρ' ρL' g' hg' hPP' hρL', hx, hx']
    exact hxx

  obtain ⟨i, hi, hIso, ib, hib, hibf, uA, huA, huAg, i₁, j₁, hcorr⟩ :=
    hR3i L ((φL.restrictScalars 𝒪).comp ψA) hψL (hconn_local L) uL uL' ρL ρL' hLeq

  have hdL : ρL.d = ρ.d := StratEq.IsPullbackVia.d_eq (φL.restrictScalars 𝒪) g hg ρ ρL hρL
  have hdL' : ρL'.d = ρ'.d := StratEq.IsPullbackVia.d_eq (φL.restrictScalars 𝒪) g' hg' ρ' ρL' hρL'
  let ρs := StratEq.pad hΛℤ j₁ (ρ'.d + i₁) ρ
  let ρs' := StratEq.pad hΛℤ i₁ (ρ.d + j₁) ρ'
  let ρsL := StratEq.pad hΛℤ j₁ (ρ'.d + i₁) ρL
  let ρsL' := StratEq.pad hΛℤ i₁ (ρ.d + j₁) ρL'
  have hds : ρs.d = ρ.d + j₁ + (ρ'.d + i₁) := rfl
  have hds' : ρs'.d = ρ.d + j₁ + (ρ'.d + i₁) := by show ρ'.d + i₁ + (ρ.d + j₁) = _; omega
  have hdsL : ρsL.d = ρ.d + j₁ + (ρ'.d + i₁) := by show ρL.d + j₁ + (ρ'.d + i₁) = _; rw [hdL]
  have hdsL' : ρsL'.d = ρ.d + j₁ + (ρ'.d + i₁) := by show ρL'.d + i₁ + (ρ.d + j₁) = _; rw [hdL']; omega
  have h0L : algebraMap C L (algebraMap 𝒪 C π) = 0 := by
    rw [IsScalarTower.algebraMap_apply C A L, hπA, map_zero]
  refine ⟨ρ.d + j₁ + (ρ'.d + i₁), ptX _ A ψA rfl u ρs hds hπA, ptX _ A ψA rfl u' ρs' hds' hπA, ?_, ?_, ?_⟩
  ·
    rw [hx1, ← hx]
    obtain ⟨ib₀, hib₀, hib₀f, uA₀, huA₀, huA₀g, i₀, j₀, hc₀⟩ := StratEq.corr_pad hΛℤ j₁ (ρ'.d + i₁) ρ
    exact hR1 A ψA rfl u u ρs ρ (Iso.refl _) (Category.id_comp _) (StratEq.isoVia_refl u _)
      ⟨ib₀, hib₀, hib₀f, uA₀, huA₀, huA₀g, i₀, j₀, hc₀⟩
  · rw [hx1, ← hx']
    obtain ⟨ib₀, hib₀, hib₀f, uA₀, huA₀, huA₀g, i₀, j₀, hc₀⟩ := StratEq.corr_pad hΛℤ i₁ (ρ.d + j₁) ρ'
    exact hR1 A ψA rfl u' u' ρs' ρ' (Iso.refl _) (Category.id_comp _) (StratEq.isoVia_refl u' _)
      ⟨ib₀, hib₀, hib₀f, uA₀, huA₀, huA₀g, i₀, j₀, hc₀⟩
  ·
    have e1 := hx2 _ A L φL ψA rfl hψL u uL ρs ρsL g hg hds hdsL hπA h0L hPP
      (StratEq.isPullbackVia_pad hΛℤ j₁ (ρ'.d + i₁) (φL.restrictScalars 𝒪) g hg ρ ρL hρL)
    have e2 := hx2 _ A L φL ψA rfl hψL u' uL' ρs' ρsL' g' hg' hds' hdsL' hπA h0L hPP'
      (StratEq.isPullbackVia_pad hΛℤ i₁ (ρ.d + j₁) (φL.restrictScalars 𝒪) g' hg' ρ' ρL' hρL')
    show Spec.map (CommRingCat.ofHom (φL : A →+* L)) ≫ _ = Spec.map (CommRingCat.ofHom (φL : A →+* L)) ≫ _
    rw [← e1, ← e2]
    have key : ptX _ L ((φL.restrictScalars 𝒪).comp ψA) hψL uL ρsL hdsL h0L =
        ptX _ L ((φL.restrictScalars 𝒪).comp ψA) hψL uL' ρsL' hdsL' h0L := by
      refine (hx4 _ L ((φL.restrictScalars 𝒪).comp ψA) hψL h0L uL uL' ρsL ρsL' hdsL hdsL').mpr
        ⟨i, hi, hIso, ib, hib, hibf, uA, huA, huAg, ?_⟩

      obtain ⟨_, _, hactA, _⟩ := huA
      show ib ≫ (ρL'.φ ≫ ρL'.Ab.act _) ≫ uA = ρL.φ ≫ ρL.Ab.act _
      simp only [Category.assoc]
      rw [hactA]
      exact hcorr
    rw [key]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_strata_point_specMap_comp_eq_of_atPrime_map_eq_of_rigidifiedToG
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_strata_point_specMap_comp_eq_of_atPrime_map_eq_of_rigidifiedToG (solution)
