-- Prove2me | solution 1 for CuspForm.TWLevel.HeckeRing.finite_and_isLocalRing_and_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/cd5c68bd-c6e0-54cf-a833-e8794cadd9ee

import Mathlib
import Definitions.Def_CuspForm_TWLevelHeckeRing
import Theorems.Thm_MonoidAlgebra_isLocalRing_of_isPGroup
import Theorems.Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite
import Theorems.Thm_CohCarrier_HeckeData_finite_ML_and_free_ML
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete
p2m_attr_erase "instance" "IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing"
p2m_attr_erase "simp" "IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open IsLocalRing

namespace TQStruct

theorem idem_trivial_of_isLocalRing {R : Type*} [Ring R] [IsLocalRing R] {e : R}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := e) (b := 1 - e) (by abel) with hu | hu
  · right
    have := hu.mul_left_cancel (hmul.trans (mul_zero e).symm)
    exact (sub_eq_zero.mp this).symm
  · left
    have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
    exact hu.mul_left_cancel (h2.trans (mul_zero _).symm)

theorem isLocalRing_of_idem_trivial {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    [Nontrivial A] (h : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing A := by
  classical
  obtain ⟨-, hbij, -, -⟩ :=
    Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite (𝒪 := 𝒪) A
  set Φ := RingHom.pi fun I : MaximalSpectrum A => algebraMap A (Localization.AtPrime I.asIdeal)
  change Function.Bijective Φ at hbij

  have huniq : ∀ I J : MaximalSpectrum A, I = J := by
    intro I J
    by_contra hIJ
    obtain ⟨e, he⟩ := hbij.2 (Pi.single I 1)
    have hidem : IsIdempotentElem e := by
      apply hbij.1
      show Φ (e * e) = Φ e
      rw [map_mul, he, ← Pi.single_mul, mul_one]
    rcases h e hidem with h0 | h1
    · have := congrFun he I
      rw [h0, map_zero, Pi.zero_apply, Pi.single_eq_same] at this
      exact zero_ne_one this
    · have := congrFun he J
      rw [h1, map_one, Pi.one_apply, Pi.single_eq_of_ne (Ne.symm hIJ)] at this
      exact one_ne_zero this
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' => ?_⟩
  have := huniq ⟨M', hM'⟩ ⟨M, hM⟩
  exact congrArg MaximalSpectrum.asIdeal this

theorem finite_end {𝒪 : Type*} [CommRing 𝒪] [IsNoetherianRing 𝒪] (M : Type*) [AddCommGroup M]
    [Module 𝒪 M] [Module.Finite 𝒪 M] : Module.Finite 𝒪 (Module.End 𝒪 M) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' 𝒪 M
  have hinj : Function.Injective (LinearMap.lcomp 𝒪 M π : Module.End 𝒪 M →ₗ[𝒪] ((Fin n → 𝒪) →ₗ[𝒪] M)) := by
    intro f g hfg
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    exact congrArg (fun h : (Fin n → 𝒪) →ₗ[𝒪] M => h y) hfg
  exact Module.Finite.of_injective _ hinj

theorem isNoetherianRing_of_finite {𝒪 : Type*} [CommRing 𝒪] [IsNoetherianRing 𝒪] (A : Type*)
    [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] : IsNoetherianRing A := by
  have : IsNoetherian 𝒪 A := inferInstance
  exact isNoetherian_of_tower 𝒪 this

section Loc

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {V : Type} [AddCommGroup V] [Module 𝒪 V]
  (D : CohCarrier.HeckeData 𝒪 V (ResidueField 𝒪))

theorem exists_sub_algebraMap_mem_maximalIdeal (z : Localization D.mTheta.primeCompl) :
    ∃ a : 𝒪, z - algebraMap 𝒪 _ a ∈ maximalIdeal (Localization D.mTheta.primeCompl) := by
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective D.mTheta.primeCompl z
  have hs : D.thetaTilde s ≠ 0 := fun h => s.2 (by
    show (s : D.FreeAlg) ∈ RingHom.ker D.thetaTilde.toRingHom
    exact h)
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (D.thetaTilde f * (D.thetaTilde s)⁻¹)
  refine ⟨a, ?_⟩
  have hmem : f - MvPolynomial.C a * (s : D.FreeAlg) ∈ D.mTheta := by
    show f - MvPolynomial.C a * (s : D.FreeAlg) ∈ RingHom.ker D.thetaTilde.toRingHom
    rw [RingHom.mem_ker]
    show D.thetaTilde (f - MvPolynomial.C a * (s : D.FreeAlg)) = 0
    rw [map_sub, map_mul, show (MvPolynomial.C a : D.FreeAlg) = algebraMap 𝒪 D.FreeAlg a from rfl,
      AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha, inv_mul_cancel_right₀ hs, sub_self]
  have heq : IsLocalization.mk' (Localization D.mTheta.primeCompl) f s - algebraMap 𝒪 _ a =
      IsLocalization.mk' (Localization D.mTheta.primeCompl) (f - MvPolynomial.C a * (s : D.FreeAlg)) s := by
    have hu : algebraMap D.FreeAlg (Localization D.mTheta.primeCompl) (s : D.FreeAlg) *
        IsLocalization.mk' (Localization D.mTheta.primeCompl) 1 s = 1 := by
      rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_self']
    rw [IsScalarTower.algebraMap_apply 𝒪 D.FreeAlg (Localization D.mTheta.primeCompl),
      show algebraMap 𝒪 D.FreeAlg a = MvPolynomial.C a from rfl,
      IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_mul_mk'_one (x := f - _), map_sub, map_mul,
      sub_mul, mul_assoc, hu, mul_one]
  rw [heq]
  exact (IsLocalization.AtPrime.mk'_mem_maximal_iff _ D.mTheta _ s).mpr hmem

theorem algebraMap_mem_maximalIdeal_loc {a : 𝒪} (ha : a ∈ maximalIdeal 𝒪) :
    algebraMap 𝒪 (Localization D.mTheta.primeCompl) a ∈ maximalIdeal (Localization D.mTheta.primeCompl) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 D.FreeAlg (Localization D.mTheta.primeCompl)]
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff _ D.mTheta _).mpr
  show algebraMap 𝒪 D.FreeAlg a ∈ RingHom.ker D.thetaTilde.toRingHom
  rw [RingHom.mem_ker]
  show D.thetaTilde (algebraMap 𝒪 D.FreeAlg a) = 0
  rw [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).mpr ha]

end Loc

section TW

open CuspForm.TWLevel

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
  (p : ℕ) (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
  [NeZero N] [NeZero r] [∀ i, NeZero (qv i)]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* ResidueField 𝒪) (α : Fin t → ResidueField 𝒪)
  (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))

abbrev MQ : Type := ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ
abbrev Loc : Type := Localization (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ).mTheta.primeCompl

def φL : Loc N r qv S 𝒪 p πΔ θ α hcQ →ₐ[𝒪] Module.End 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ) :=
  Algebra.lsmul 𝒪 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ)

@[scoped simp] theorem φL_apply (a : Loc N r qv S 𝒪 p πΔ θ α hcQ) (x : MQ N r qv S 𝒪 p πΔ θ α hcQ) :
    φL N r qv S 𝒪 p πΔ θ α hcQ a x = a • x := rfl

theorem diaML_smul_loc (u : (ZMod (level N r qv))ˣ) (a : Loc N r qv S 𝒪 p πΔ θ α hcQ)
    (x : MQ N r qv S 𝒪 p πΔ θ α hcQ) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u (a • x) =
      a • diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u x :=
  LinearMap.map_smul (LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u)) a x

theorem diaML_one' : diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc 1 = 1 := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc 1) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    congr 1
    show CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 1 m = m
    rw [CohCarrier.diamondL_eq_diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 1 1 (map_one _) m]
    ext γ
    show m (Additive.ofMul (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) 1 (Additive.toMul γ))) = m γ
    congr 1
    have : CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) 1 (Additive.toMul γ) = Additive.toMul γ :=
      Subtype.ext (by simp [CohCarrier.conjHom])
    rw [this]
    rfl

theorem diaML_eq_of_piQ_eq {u v : (ZMod (level N r qv))ˣ} (hu : u ∈ HR N r qv) (hv : v ∈ HR N r qv)
    (h : piQ N r qv p πΔ u = piQ N r qv p πΔ v) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u = diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc v := by

  have hw : u * v⁻¹ ∈ HQ N r qv p πΔ := by
    rw [mem_HQ_iff]
    exact ⟨mul_mem hu (inv_mem hv), by rw [map_mul, map_inv, h, mul_inv_cancel]⟩
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective (level N r qv) (u * v⁻¹)
  obtain ⟨τ, hτ⟩ := CohCarrier.gamma0Units_surjective (level N r qv) v
  have hστ : CohCarrier.gamma0Units (level N r qv) (τ * σ) = u := by
    rw [map_mul, hσ, hτ, mul_comm, inv_mul_cancel_right]
  have hσH : (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ CohCarrier.GammaH (level N r qv) (HQ N r qv p πΔ) := by
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨σ.2, ?_⟩
    have e : (⟨(σ : Matrix.SpecialLinearGroup (Fin 2) ℤ), σ.2⟩ :
        ↥(CongruenceSubgroup.Gamma0 (level N r qv))) = σ := Subtype.coe_eta _ _
    rw [e, hσ]
    exact hw
  set κ : ↥(CohCarrier.GammaH (level N r qv) (HQ N r qv p πΔ)) :=
    ⟨(σ : Matrix.SpecialLinearGroup (Fin 2) ℤ), hσH⟩ with hκ
  have hraw : ∀ m : Carrier N r qv 𝒪 (HQ N r qv p πΔ),
      CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 u m =
        CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 v m := by
    intro m
    rw [CohCarrier.diamondL_eq_diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 u (τ * σ) hστ m,
      CohCarrier.diamondL_eq_diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 v τ hτ m]
    ext γ
    show m (Additive.ofMul (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) (τ * σ) (Additive.toMul γ))) =
      m (Additive.ofMul (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) τ (Additive.toMul γ)))
    have hconj : CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) (τ * σ) (Additive.toMul γ) =
        CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) τ (κ * Additive.toMul γ * κ⁻¹) :=
      Subtype.ext (by
        simp only [CohCarrier.conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, hκ,
          InvMemClass.coe_inv, mul_inv_rev]
        group)
    rw [hconj, map_mul (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) τ),
      map_mul (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) τ),
      map_inv (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) τ), ofMul_mul, ofMul_mul, ofMul_inv,
      map_add, map_add, map_neg]
    simp only [ofMul_toMul, add_neg_cancel_comm]
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u) (LocalizedModule.mk m s) =
      LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc v) (LocalizedModule.mk m s)
    rw [LocalizedModule.map_mk, LocalizedModule.map_mk]
    congr 1
    exact hraw m

theorem diaML_mul' (u v : (ZMod (level N r qv))ˣ) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc (u * v) =
      diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u * diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc v := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective (level N r qv) u
  obtain ⟨τ, hτ⟩ := CohCarrier.gamma0Units_surjective (level N r qv) v
  have hστ : CohCarrier.gamma0Units (level N r qv) (τ * σ) = u * v := by rw [map_mul, hσ, hτ, mul_comm]
  have hraw : ∀ m : Carrier N r qv 𝒪 (HQ N r qv p πΔ),
      CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 (u * v) m =
        CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 u
          (CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 v m) := by
    intro m
    rw [CohCarrier.diamondL_eq_diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 (u * v) (τ * σ) hστ m,
      CohCarrier.diamondL_eq_diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 v τ hτ m,
      CohCarrier.diamondL_eq_diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 u σ hσ]
    ext γ
    show m (Additive.ofMul (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) (τ * σ) (Additive.toMul γ))) =
      m (Additive.ofMul (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) τ
        (CohCarrier.conjHom (level N r qv) (HQ N r qv p πΔ) σ (Additive.toMul γ))))
    congr 2
    apply Subtype.ext
    simp only [CohCarrier.conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
    group
  apply LinearMap.ext
  intro z
  rw [Module.End.mul_apply]
  induction z using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc (u * v))
        (LocalizedModule.mk m s) =
      LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u)
        (LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc v) (LocalizedModule.mk m s))
    rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
    congr 1
    exact hraw m

def Gsub : Subgroup (Delta qv p) := (HR N r qv).map (piQ N r qv p πΔ)

theorem piQ_mem_Gsub {u : (ZMod (level N r qv))ˣ} (hu : u ∈ HR N r qv) :
    piQ N r qv p πΔ u ∈ Gsub N r qv p πΔ := Subgroup.mem_map_of_mem _ hu

def gOf {u : (ZMod (level N r qv))ˣ} (hu : u ∈ HR N r qv) : ↥(Gsub N r qv p πΔ) :=
  ⟨piQ N r qv p πΔ u, piQ_mem_Gsub N r qv p πΔ hu⟩

theorem exists_gOf_eq (g : ↥(Gsub N r qv p πΔ)) : ∃ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
    gOf N r qv p πΔ hu = g := by
  obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp g.2
  exact ⟨u, hu, Subtype.ext hug⟩

def δΔ : ↥(Gsub N r qv p πΔ) → Module.End 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ) := fun g =>
  diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc (Classical.choose (Subgroup.mem_map.mp g.2))

theorem δΔ_gOf {u : (ZMod (level N r qv))ˣ} (hu : u ∈ HR N r qv) :
    δΔ N r qv S 𝒪 p πΔ θ α hcQ hdc (gOf N r qv p πΔ hu) =
      diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u := by
  have h1 := (Classical.choose_spec (Subgroup.mem_map.mp (gOf N r qv p πΔ hu).2)).1
  have h2 := (Classical.choose_spec (Subgroup.mem_map.mp (gOf N r qv p πΔ hu).2)).2
  exact diaML_eq_of_piQ_eq N r qv S 𝒪 p πΔ θ α hcQ hdc h1 hu h2

def δΔHom : ↥(Gsub N r qv p πΔ) →* Module.End 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ) where
  toFun := δΔ N r qv S 𝒪 p πΔ θ α hcQ hdc
  map_one' := by
    have h1 : gOf N r qv p πΔ (one_mem (HR N r qv)) = 1 := Subtype.ext (map_one _)
    rw [← h1, δΔ_gOf N r qv S 𝒪 p πΔ θ α hcQ hdc (one_mem _)]
    exact diaML_one' N r qv S 𝒪 p πΔ θ α hcQ hdc
  map_mul' x y := by
    obtain ⟨u, hu, rfl⟩ := exists_gOf_eq N r qv p πΔ x
    obtain ⟨v, hv, rfl⟩ := exists_gOf_eq N r qv p πΔ y
    have hxy : gOf N r qv p πΔ (mul_mem hu hv) = gOf N r qv p πΔ hu * gOf N r qv p πΔ hv :=
      Subtype.ext (map_mul _ u v)
    rw [← hxy, δΔ_gOf N r qv S 𝒪 p πΔ θ α hcQ hdc (mul_mem hu hv),
      δΔ_gOf N r qv S 𝒪 p πΔ θ α hcQ hdc hu, δΔ_gOf N r qv S 𝒪 p πΔ θ α hcQ hdc hv]
    exact diaML_mul' N r qv S 𝒪 p πΔ θ α hcQ hdc u v

@[scoped simp] theorem δΔHom_apply (x : ↥(Gsub N r qv p πΔ)) :
    δΔHom N r qv S 𝒪 p πΔ θ α hcQ hdc x = δΔ N r qv S 𝒪 p πΔ θ α hcQ hdc x := rfl

theorem φL_mul_δΔHom (x : Loc N r qv S 𝒪 p πΔ θ α hcQ) (g : ↥(Gsub N r qv p πΔ)) :
    φL N r qv S 𝒪 p πΔ θ α hcQ x * δΔHom N r qv S 𝒪 p πΔ θ α hcQ hdc g =
      δΔHom N r qv S 𝒪 p πΔ θ α hcQ hdc g * φL N r qv S 𝒪 p πΔ θ α hcQ x := by
  obtain ⟨u, hu, rfl⟩ := exists_gOf_eq N r qv p πΔ g
  apply LinearMap.ext
  intro z
  rw [Module.End.mul_apply, Module.End.mul_apply, φL_apply, φL_apply, δΔHom_apply,
    δΔ_gOf N r qv S 𝒪 p πΔ θ α hcQ hdc hu, diaML_smul_loc]

def Ψ : MonoidAlgebra (Loc N r qv S 𝒪 p πΔ θ α hcQ) ↥(Gsub N r qv p πΔ) →+* Module.End 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ) :=
  MonoidAlgebra.liftNCRingHom (φL N r qv S 𝒪 p πΔ θ α hcQ).toRingHom
    (δΔHom N r qv S 𝒪 p πΔ θ α hcQ hdc) (fun x y => φL_mul_δΔHom N r qv S 𝒪 p πΔ θ α hcQ hdc x y)

theorem Ψ_single (g : ↥(Gsub N r qv p πΔ)) (a : Loc N r qv S 𝒪 p πΔ θ α hcQ) :
    Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc (MonoidAlgebra.single g a) =
      φL N r qv S 𝒪 p πΔ θ α hcQ a * δΔHom N r qv S 𝒪 p πΔ θ α hcQ hdc g :=
  MonoidAlgebra.liftNC_single _ _ g a

theorem Ψ_single_one (a : Loc N r qv S 𝒪 p πΔ θ α hcQ) :
    Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc (MonoidAlgebra.single 1 a) = φL N r qv S 𝒪 p πΔ θ α hcQ a := by
  rw [Ψ_single, (δΔHom N r qv S 𝒪 p πΔ θ α hcQ hdc).map_one, mul_one]

theorem Ψ_algebraMap (a : 𝒪) :
    Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc (MonoidAlgebra.single 1 (algebraMap 𝒪 (Loc N r qv S 𝒪 p πΔ θ α hcQ) a)) =
      algebraMap 𝒪 (Module.End 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ)) a := by
  rw [Ψ_single_one, AlgHom.commutes]

def aug : MonoidAlgebra (Loc N r qv S 𝒪 p πΔ θ α hcQ) ↥(Gsub N r qv p πΔ) →ₐ[Loc N r qv S 𝒪 p πΔ θ α hcQ]
    Loc N r qv S 𝒪 p πΔ θ α hcQ :=
  MonoidAlgebra.lift _ _ _ 1

theorem aug_single_one (a : Loc N r qv S 𝒪 p πΔ θ α hcQ) :
    aug N r qv S 𝒪 p πΔ θ α hcQ (MonoidAlgebra.single 1 a) = a := by
  rw [aug, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

theorem not_isUnit_of_aug {y : MonoidAlgebra (Loc N r qv S 𝒪 p πΔ θ α hcQ) ↥(Gsub N r qv p πΔ)}
    (hy : aug N r qv S 𝒪 p πΔ θ α hcQ y ∈ maximalIdeal (Loc N r qv S 𝒪 p πΔ θ α hcQ)) : ¬ IsUnit y :=
  fun h => (IsLocalRing.mem_maximalIdeal _).mp hy (h.map _)

variable [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

theorem isPGroup_delta : IsPGroup p (Delta qv p) := by
  classical
  apply IsPGroup.of_card (n := ∑ i, padicValNat p (qv i - 1))
  rw [Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact Finset.prod_pow_eq_pow_sum _ _ _

include hp𝒪 in

theorem isLocalRing_monoidAlgebra :
    IsLocalRing (MonoidAlgebra (Loc N r qv S 𝒪 p πΔ θ α hcQ) ↥(Gsub N r qv p πΔ)) := by
  apply MonoidAlgebra.isLocalRing_of_isPGroup (p := p) _ ((isPGroup_delta qv p).to_subgroup _)
  have := algebraMap_mem_maximalIdeal_loc (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) hp𝒪
  rwa [map_natCast] at this

variable [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

theorem finite_MQ : Module.Finite 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ) := by
  haveI : Module.Finite 𝒪 (Carrier N r qv 𝒪 (HQ N r qv p πΔ)) :=
    CohCarrier.H1_moduleFinite (level N r qv) (HQ N r qv p πΔ) 𝒪 𝒪
  exact (CohCarrier.HeckeData.finite_ML_and_free_ML (k := ResidueField 𝒪) IsLocalRing.residue_surjective
    (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ)).1

include hp𝒪 in

theorem structure_of_embedding [Nontrivial (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ)]
    (T : Type) [CommRing T] [Algebra 𝒪 T]
    (ι : T →ₐ[𝒪] Module.End 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ)) (hinj : Function.Injective ι)
    (hle : ∀ x, ι x ∈ Set.range (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc)) :
    ∃ (_ : IsLocalRing T), IsNoetherianRing T ∧ Module.Finite 𝒪 T ∧
      IsLocalHom (algebraMap 𝒪 T) ∧ Function.Surjective (residue T ∘ algebraMap 𝒪 T) ∧
      IsAdicComplete (maximalIdeal T) T := by

  haveI hAloc := isLocalRing_monoidAlgebra N r qv S 𝒪 p πΔ θ α hcQ hp𝒪

  haveI : Nontrivial T := ⟨⟨0, 1, fun h => zero_ne_one (by rw [← map_zero ι, h, map_one])⟩⟩

  have hker : ∀ z, (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) z = 0 → z ∈ maximalIdeal _ := by
    intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc)
    rw [hz] at this
    exact not_isUnit_zero this

  haveI hfin : Module.Finite 𝒪 T := by
    haveI := finite_MQ N r qv S 𝒪 p πΔ θ α hcQ
    haveI := finite_end (𝒪 := 𝒪) (MQ N r qv S 𝒪 p πΔ θ α hcQ)
    haveI : IsNoetherian 𝒪 (Module.End 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ)) := inferInstance
    exact Module.Finite.of_injective ι.toLinearMap hinj

  have hlift : ∀ x : T, ∃ y, (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) y = ι x := fun x => hle x

  have hunit : ∀ (x : T) (y : MonoidAlgebra (Loc N r qv S 𝒪 p πΔ θ α hcQ) ↥(Gsub N r qv p πΔ)),
      (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) y = ι x → IsUnit x → IsUnit y := by
    intro x y hy hx
    obtain ⟨y', hy'⟩ := hlift (↑(hx.unit⁻¹) : T)
    have hz : (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) (y * y' - 1) = 0 := by
      rw [map_sub, map_mul, hy, hy', ← map_mul, IsUnit.mul_val_inv, map_one, map_one, sub_self]
    have hm := hker _ hz
    have h1 : IsUnit (y * y') := by
      have h2 : y * y' = 1 - -(y * y' - 1) := by abel
      rw [h2]
      exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(y * y' - 1))
        ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hm))
    obtain ⟨w, hw⟩ := h1
    have h3 : y * (y' * ↑w⁻¹) = 1 := by rw [← mul_assoc, ← hw, Units.mul_inv]
    haveI : IsDedekindFiniteMonoid (MonoidAlgebra (Loc N r qv S 𝒪 p πΔ θ α hcQ) ↥(Gsub N r qv p πΔ)) :=
      ⟨fun {a b} h => (mul_comm b a).trans h⟩
    exact .of_mul_eq_one _ h3

  have hidem : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨y, hy⟩ := hlift e
    have hz : (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) (y * y - y) = 0 := by
      rw [map_sub, map_mul, hy, ← map_mul, he.eq, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with hu | hu
    · right
      apply hinj
      rw [← hy, map_one]
      have hv : (↑(hu.unit⁻¹) : MonoidAlgebra (Loc N r qv S 𝒪 p πΔ θ α hcQ) ↥(Gsub N r qv p πΔ)) * y = 1 :=
        hu.val_inv_mul
      have h1 : y - 1 = ↑(hu.unit⁻¹) * (y * y - y) := by linear_combination (1 - y) * hv
      have := congrArg (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) h1
      rw [map_mul, hz, mul_zero, map_sub, map_one, sub_eq_zero] at this
      exact this
    · left
      apply hinj
      rw [← hy, map_zero]
      have hv : (↑(hu.unit⁻¹) : MonoidAlgebra (Loc N r qv S 𝒪 p πΔ θ α hcQ) ↥(Gsub N r qv p πΔ)) * (1 - y) = 1 :=
        hu.val_inv_mul
      have h1 : y = -(↑(hu.unit⁻¹) * (y * y - y)) := by linear_combination (-y) * hv
      have := congrArg (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) h1
      rw [map_neg, map_mul, hz, mul_zero, neg_zero] at this
      exact this
  haveI hTloc : IsLocalRing T := isLocalRing_of_idem_trivial (𝒪 := 𝒪) T hidem

  have hlh : IsLocalHom (algebraMap 𝒪 T) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : a ∈ maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal a).mpr hna
    have hy₀ : (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) (MonoidAlgebra.single 1 (algebraMap 𝒪 (Loc N r qv S 𝒪 p πΔ θ α hcQ) a)) =
        ι (algebraMap 𝒪 T a) := by
      rw [Ψ_algebraMap, AlgHom.commutes]
    apply not_isUnit_of_aug N r qv S 𝒪 p πΔ θ α hcQ (y := MonoidAlgebra.single 1 (algebraMap 𝒪 _ a))
    · rw [aug_single_one]
      exact algebraMap_mem_maximalIdeal_loc _ hmem
    · exact hunit _ _ hy₀ ha
  haveI := hlh

  have hres : Function.Surjective (residue T ∘ algebraMap 𝒪 T) := by
    intro x
    induction x using Quotient.inductionOn' with
    | h x =>
      obtain ⟨y, hy⟩ := hlift x
      obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal
        (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) (aug N r qv S 𝒪 p πΔ θ α hcQ y)
      refine ⟨a, ?_⟩
      show residue T (algebraMap 𝒪 T a) = residue T x
      rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
      intro hu
      have hy' : (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) (y - MonoidAlgebra.single 1 (algebraMap 𝒪 (Loc N r qv S 𝒪 p πΔ θ α hcQ) a)) =
          ι (x - algebraMap 𝒪 T a) := by
        simp only [map_sub, hy, Ψ_algebraMap, AlgHom.commutes]
      apply not_isUnit_of_aug N r qv S 𝒪 p πΔ θ α hcQ
        (y := y - MonoidAlgebra.single 1 (algebraMap 𝒪 (Loc N r qv S 𝒪 p πΔ θ α hcQ) a))
      · simpa only [map_sub, aug_single_one] using ha
      · exact hunit _ _ hy' hu
  refine ⟨hTloc, isNoetherianRing_of_finite (𝒪 := 𝒪) T, hfin, hlh, hres, ?_⟩
  exact IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪) (T := T)

theorem opFree_mem_range (f : (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ).FreeAlg) :
    Algebra.lsmul 𝒪 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ) f ∈ Set.range (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) := by
  refine ⟨MonoidAlgebra.single 1 (algebraMap _ (Loc N r qv S 𝒪 p πΔ θ α hcQ) f), ?_⟩
  rw [Ψ_single_one]
  apply LinearMap.ext
  intro x
  rw [φL_apply, Algebra.lsmul_coe]
  exact IsScalarTower.algebraMap_smul _ f x

theorem diaML_mem_range {u : (ZMod (level N r qv))ˣ} (hu : u ∈ HR N r qv) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u ∈ Set.range (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) := by
  refine ⟨MonoidAlgebra.single (gOf N r qv p πΔ hu) 1, ?_⟩
  rw [Ψ_single, map_one, one_mul, δΔHom_apply, δΔ_gOf N r qv S 𝒪 p πΔ θ α hcQ hdc hu]

theorem mem_range_of_mem {a : Module.End 𝒪 (MQ N r qv S 𝒪 p πΔ θ α hcQ)}
    (ha : a ∈ heckeSubalgebra N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) :
    a ∈ Set.range (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) := by
  refine Algebra.adjoin_induction (p := fun a _ => a ∈ Set.range (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc))
    ?_ ?_ ?_ ?_ ha
  · rintro a (⟨ℓ, hℓ, hℓS, hℓL, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact opFree_mem_range N r qv S 𝒪 p πΔ θ α hcQ hdc _
    · exact diaML_mem_range N r qv S 𝒪 p πΔ θ α hcQ hdc hu
  · intro c
    exact ⟨MonoidAlgebra.single 1 (algebraMap 𝒪 (Loc N r qv S 𝒪 p πΔ θ α hcQ) c),
      Ψ_algebraMap N r qv S 𝒪 p πΔ θ α hcQ hdc c⟩
  · rintro a b _ _ ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, by rw [map_add, hy, hz]⟩
  · rintro a b _ _ ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y * z, by rw [map_mul, hy, hz]⟩

theorem act_mem_range (x : HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) :
    HeckeRing.act N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc x ∈ Set.range (Ψ N r qv S 𝒪 p πΔ θ α hcQ hdc) :=
  mem_range_of_mem N r qv S 𝒪 p πΔ θ α hcQ hdc x.2

end TW

end TQStruct
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete.TQStruct"

open Polynomial IsLocalRing CuspForm.TWLevel

open TQStruct in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (α : Fin t → ResidueField 𝒪)
    (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
    (hM : Nontrivial (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ)) :
    Module.Finite 𝒪 (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ∧
    IsNoetherianRing (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ∧
    ∃ _ : IsLocalRing (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc),
      IsAdicComplete (maximalIdeal (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc))
        (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ∧
      IsLocalHom (algebraMap 𝒪 (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)) ∧
      Function.Surjective (residue (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ∘
        algebraMap 𝒪 (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)) := by
  haveI := hM
  obtain ⟨hloc, hnoe, hfin, hlh, hres, hcpl⟩ :=
    structure_of_embedding N r qv S 𝒪 p πΔ θ α hcQ hdc hp𝒪
      (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)
      (HeckeRing.act N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)
      (HeckeRing.act_injective N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)
      (act_mem_range N r qv S 𝒪 p πΔ θ α hcQ hdc)
  exact ⟨hfin, hnoe, hloc, hcpl, hlh, hres⟩

end
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete.TQStruct"

end S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete
end P2MW
export P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete (solution)
