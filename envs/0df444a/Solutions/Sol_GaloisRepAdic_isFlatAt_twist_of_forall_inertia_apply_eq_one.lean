-- Prove2me | solution 1 for GaloisRepAdic.isFlatAt_twist_of_forall_inertia_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/318418cf-5d08-5cdf-8648-834016f9032a

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Twist
import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Theorems.Thm_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr
import Theorems.Thm_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one

set_option autoImplicit false

namespace P2mFlatTwist

abbrev Γℚ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

scoped instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

section level

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem levelAction_mk (ρ : GaloisRepAdic A) (I : Ideal A) (σ : Γℚ) (v : ρ.V) :
    ρ.levelAction I σ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ.ρ σ v) := rfl

def Lvl (ρ : GaloisRepAdic A) (I : Ideal A) : Type := ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))

noncomputable scoped instance (ρ : GaloisRepAdic A) (I : Ideal A) : AddCommGroup (Lvl ρ I) :=
  inferInstanceAs (AddCommGroup (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))))

noncomputable scoped instance (ρ : GaloisRepAdic A) (I : Ideal A) : Module A (Lvl ρ I) :=
  inferInstanceAs (Module A (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))))

noncomputable scoped instance (ρ : GaloisRepAdic A) (I : Ideal A) : Module (A ⧸ I) (Lvl ρ I) :=
  inferInstanceAs (Module (A ⧸ I) (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))))

noncomputable scoped instance levelDistribMulAction (ρ : GaloisRepAdic A) (I : Ideal A) :
    DistribMulAction Γℚ (Lvl ρ I) where
  smul σ m := ρ.levelAction I σ m
  one_smul m := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change ρ.levelAction I 1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    rw [levelAction_mk, map_one, Module.End.one_apply]
  mul_smul σ τ m := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change ρ.levelAction I (σ * τ) (Submodule.Quotient.mk v) =
      ρ.levelAction I σ (ρ.levelAction I τ (Submodule.Quotient.mk v))
    rw [levelAction_mk, levelAction_mk, levelAction_mk, map_mul, Module.End.mul_apply]
  smul_zero σ := map_zero (ρ.levelAction I σ)
  smul_add σ x y := map_add (ρ.levelAction I σ) x y

theorem lvl_smul_def (ρ : GaloisRepAdic A) (I : Ideal A) (σ : Γℚ) (m : Lvl ρ I) :
    σ • m = ρ.levelAction I σ m := rfl

theorem lvl_smul_smul_comm (ρ : GaloisRepAdic A) (I : Ideal A) (σ : Γℚ) (a : A) (m : Lvl ρ I) :
    σ • (a • m) = a • (σ • m) :=
  (ρ.levelAction I σ).map_smul a m

theorem lvl_mk_smul (ρ : GaloisRepAdic A) (I : Ideal A) (a : A) (m : Lvl ρ I) :
    (Ideal.Quotient.mk I a) • m = a • m := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (p := (I • (⊤ : Submodule A ρ.V))) m
  rfl

theorem lvl_smul_smul_comm' (ρ : GaloisRepAdic A) (I : Ideal A) (σ : Γℚ) (b : A ⧸ I)
    (m : Lvl ρ I) : σ • (b • m) = b • (σ • m) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [lvl_mk_smul, lvl_mk_smul, lvl_smul_smul_comm]

theorem levelAction_twist (ρ : GaloisRepAdic A) (χ : Γℚ →* Aˣ)
    (hχ : GaloisCharIsAdicContinuous A χ) (I : Ideal A) (σ : Γℚ)
    (m : ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) :
    (ρ.twist χ hχ).levelAction I σ m = ((χ σ : Aˣ) : A) • ρ.levelAction I σ m := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rfl

def untw (ρ : GaloisRepAdic A) (χ : Γℚ →* Aˣ) (hχ : GaloisCharIsAdicContinuous A χ) (I : Ideal A)
    (m : Lvl (ρ.twist χ hχ) I) : Lvl ρ I := m

theorem untw_injective (ρ : GaloisRepAdic A) (χ : Γℚ →* Aˣ) (hχ : GaloisCharIsAdicContinuous A χ)
    (I : Ideal A) : Function.Injective (untw ρ χ hχ I) := fun _ _ h => h

theorem untw_add (ρ : GaloisRepAdic A) (χ : Γℚ →* Aˣ) (hχ : GaloisCharIsAdicContinuous A χ)
    (I : Ideal A) (m m' : Lvl (ρ.twist χ hχ) I) :
    untw ρ χ hχ I (m + m') = untw ρ χ hχ I m + untw ρ χ hχ I m' := rfl

theorem untw_zero (ρ : GaloisRepAdic A) (χ : Γℚ →* Aˣ) (hχ : GaloisCharIsAdicContinuous A χ)
    (I : Ideal A) : untw ρ χ hχ I 0 = 0 := rfl

theorem untw_smul (ρ : GaloisRepAdic A) (χ : Γℚ →* Aˣ) (hχ : GaloisCharIsAdicContinuous A χ)
    (I : Ideal A) (σ : Γℚ) (m : Lvl (ρ.twist χ hχ) I) :
    untw ρ χ hχ I (σ • m) = ((χ σ : Aˣ) : A) • (σ • untw ρ χ hχ I m) :=
  levelAction_twist ρ χ hχ I σ m

theorem exists_pow_maximalIdeal_le (I : Ideal A) [Finite (A ⧸ I)] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal A ^ n ≤ I := by
  by_cases hI : I = ⊤
  · exact ⟨0, hI ▸ le_top⟩
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent (Ideal.jacobson (⊥ : Ideal (A ⧸ I))) :=
    IsArtinianRing.isNilpotent_jacobson_bot
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hnil
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have hmap : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) ≤
      IsLocalRing.maximalIdeal (A ⧸ I) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_comap.mpr (map_nonunit _ a ha)
  have h2 : ((IsLocalRing.maximalIdeal A) ^ n).map (Ideal.Quotient.mk I) = ⊥ := by
    rw [Ideal.map_pow, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    exact Ideal.pow_right_mono hmap n
  rw [← Ideal.mk_ker (I := I), ← Ideal.map_eq_bot_iff_le_ker]
  exact h2

end level

def Idx {Λ : Type} [Monoid Λ] (_c : Γℚ →* Λˣ) : Type := Λˣ

scoped instance {Λ : Type} [Monoid Λ] [Finite Λ] (c : Γℚ →* Λˣ) : Finite (Idx c) :=
  inferInstanceAs (Finite Λˣ)

def Idx.val {Λ : Type} [Monoid Λ] {c : Γℚ →* Λˣ} (u : Idx c) : Λˣ := u

def Idx.mk {Λ : Type} [Monoid Λ] (c : Γℚ →* Λˣ) (u : Λˣ) : Idx c := u

@[scoped simp] theorem Idx.val_mk {Λ : Type} [Monoid Λ] (c : Γℚ →* Λˣ) (u : Λˣ) : (Idx.mk c u).val = u :=
  rfl

p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.P2mFlatTwist.Idx"
noncomputable scoped instance idxMulAction {Λ : Type} [CommMonoid Λ] (c : Γℚ →* Λˣ) : MulAction Γℚ (Idx c) where
  smul σ u := Idx.mk c (u.val * (c σ)⁻¹)
  one_smul u := by
    change Idx.mk c (u.val * (c 1)⁻¹) = u
    rw [map_one, inv_one, mul_one]
    rfl
  mul_smul σ τ u := by
    change Idx.mk c (u.val * (c (σ * τ))⁻¹) = Idx.mk c ((Idx.mk c (u.val * (c τ)⁻¹)).val * (c σ)⁻¹)
    rw [Idx.val_mk, map_mul, mul_inv_rev, mul_comm (c τ)⁻¹, ← mul_assoc, mul_right_comm]

theorem Idx.val_smul {Λ : Type} [CommMonoid Λ] (c : Γℚ →* Λˣ) (σ : Γℚ) (u : Idx c) :
    (σ • u).val = u.val * (c σ)⁻¹ := rfl

def TwFun (S N : Type) : Type := S → N

scoped instance (S N : Type) [AddCommGroup N] : AddCommGroup (TwFun S N) :=
  inferInstanceAs (AddCommGroup (S → N))

def TwFun.val {S N : Type} (φ : TwFun S N) : S → N := φ

def TwFun.mk {S N : Type} (φ : S → N) : TwFun S N := φ

@[scoped simp] theorem TwFun.val_mk {S N : Type} (φ : S → N) : (TwFun.mk φ).val = φ := rfl
p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.P2mFlatTwist.Idx P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.P2mFlatTwist.TwFun"
@[scoped simp] theorem TwFun.mk_val {S N : Type} (φ : TwFun S N) : TwFun.mk φ.val = φ := rfl

p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.P2mFlatTwist.Idx P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.P2mFlatTwist.TwFun"
theorem TwFun.ext {S N : Type} {φ ψ : TwFun S N} (h : ∀ s, φ.val s = ψ.val s) : φ = ψ :=
  funext h

theorem TwFun.val_add {S N : Type} [AddCommGroup N] (φ ψ : TwFun S N) (s : S) :
    (φ + ψ).val s = φ.val s + ψ.val s := rfl

theorem TwFun.val_zero {S N : Type} [AddCommGroup N] (s : S) : (0 : TwFun S N).val s = 0 := rfl

noncomputable scoped instance twFunDistribMulAction (S N : Type) [MulAction Γℚ S] [AddCommGroup N]
    [DistribMulAction Γℚ N] : DistribMulAction Γℚ (TwFun S N) where
  smul σ φ := TwFun.mk fun s => σ • φ.val (σ⁻¹ • s)
  one_smul φ := TwFun.ext fun s => by
    change (1 : Γℚ) • φ.val ((1 : Γℚ)⁻¹ • s) = φ.val s
    rw [inv_one, one_smul, one_smul]
  mul_smul σ τ φ := TwFun.ext fun s => by
    change (σ * τ) • φ.val ((σ * τ)⁻¹ • s) = σ • τ • φ.val (τ⁻¹ • σ⁻¹ • s)
    rw [mul_smul, mul_inv_rev, mul_smul]
  smul_zero σ := TwFun.ext fun s => by
    change σ • (0 : TwFun S N).val (σ⁻¹ • s) = 0
    rw [TwFun.val_zero, smul_zero]
  smul_add σ φ ψ := TwFun.ext fun s => by
    change σ • (φ + ψ).val (σ⁻¹ • s) = σ • φ.val (σ⁻¹ • s) + σ • ψ.val (σ⁻¹ • s)
    rw [TwFun.val_add, smul_add]

theorem TwFun.val_smul {S N : Type} [MulAction Γℚ S] [AddCommGroup N] [DistribMulAction Γℚ N]
    (σ : Γℚ) (φ : TwFun S N) (s : S) : (σ • φ).val s = σ • φ.val (σ⁻¹ • s) := rfl

end P2mFlatTwist
p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.P2mFlatTwist.Idx P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.P2mFlatTwist.TwFun P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.P2mFlatTwist"

open P2mFlatTwist in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic A) (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hχ : GaloisCharIsAdicContinuous A χ)
    (hunr : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (hflat : ρ.IsFlatAt p) :
    (ρ.twist χ hχ).IsFlatAt p := by
  classical
  obtain ⟨hfin, hlev⟩ := hflat
  refine ⟨hfin, fun I hI => ?_⟩
  haveI := hI
  obtain ⟨G, _, _, hGfin, hGflat, hGcomm, e, he_add, he_act⟩ := hlev I hI
  haveI := hGfin
  haveI := hGflat
  haveI := hGcomm
  have hp : p.Prime := Fact.out

  let χb : Γℚ →* (A ⧸ I)ˣ := (Units.map (Ideal.Quotient.mk I : A →+* A ⧸ I).toMonoidHom).comp χ
  have hχb_coe : ∀ σ : Γℚ, ((χb σ : (A ⧸ I)ˣ) : A ⧸ I) = Ideal.Quotient.mk I ((χ σ : Aˣ) : A) :=
    fun σ => rfl
  have hχb_eq_one : ∀ σ : Γℚ, ((χ σ : Aˣ) : A) - 1 ∈ I → χb σ = 1 := by
    intro σ hσ
    ext
    rw [hχb_coe, Units.val_one, ← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq]
    exact hσ

  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_le I
  obtain ⟨L, hLfin, hL⟩ := hχ n
  haveI := hLfin
  have hLK : L.fixingSubgroup ≤ χb.ker := fun σ hσ =>
    (MonoidHom.mem_ker).mpr (hχb_eq_one σ (hn (hL σ fun x hx =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ x hx)))

  have hopen : IsOpen (χb.ker : Set Γℚ) := Subgroup.isOpen_mono hLK L.fixingSubgroup_isOpen
  have hclosed : IsClosed (χb.ker : Set Γℚ) := Subgroup.isClosed_of_isOpen _ hopen
  set K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField χb.ker with hKdef
  have hfix : K.fixingSubgroup = χb.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨χb.ker, hclosed⟩
  haveI hKfin : FiniteDimensional ℚ K :=
    (InfiniteGalois.isOpen_iff_finite K).mp (by rw [hfix]; exact hopen)
  haveI hKgal : IsGalois ℚ K :=
    (InfiniteGalois.normal_iff_isGalois K).mp (by rw [hfix]; infer_instance)
  have hKχ : ∀ σ : Γℚ, (∀ x ∈ K, σ x = x) → χb σ = 1 := fun σ hσ =>
    (MonoidHom.mem_ker).mp (hfix ▸ (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ)

  have hdisc := IntermediateField.not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup K p hp
    (fun P hP σ hσ => by
      rw [hfix]
      exact (MonoidHom.mem_ker).mpr (hχb_eq_one σ (by
        rw [hunr P hP σ hσ, Units.val_one, sub_self]; exact I.zero_mem)))

  have hS : ∀ σ : Γℚ, (∀ x ∈ K, σ x = x) → ∀ u : Idx χb, σ • u = u := by
    intro σ hσ u
    change Idx.mk χb (u.val * (χb σ)⁻¹) = u
    rw [hKχ σ hσ, inv_one, mul_one]
    rfl
  obtain ⟨H₁, _, _, h₁fin, h₁flat, h₁comm, e₁, he₁_add, he₁_act⟩ :=
    GaloisRep.exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr p hp G (M := Lvl ρ I) e he_add
      (fun σ f g hfg => he_act σ f g hfg) (S := Idx χb) K hdisc hS
  haveI := h₁fin
  haveI := h₁flat
  haveI := h₁comm

  let e₂ : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      TwFun (Idx χb) (Lvl ρ I) := e₁.trans ⟨TwFun.mk, TwFun.val, fun _ => rfl, fun _ => rfl⟩
  have he₂_val : ∀ f, (e₂ f).val = e₁ f := fun f => rfl
  have he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g := fun f g =>
    TwFun.ext fun s => by rw [TwFun.val_add, he₂_val, he₂_val, he₂_val, he₁_add]; rfl
  have he₂_act : ∀ (σ : Γℚ) (f g : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H₁, g x = σ (f x)) → e₂ g = σ • e₂ f := fun σ f g hfg =>
    TwFun.ext fun s => by rw [TwFun.val_smul, he₂_val, he₂_val, he₁_act σ f g hfg]

  let W : Type := Lvl (ρ.twist χ hχ) I
  let ι : W →+ TwFun (Idx χb) (Lvl ρ I) :=
    { toFun := fun m => TwFun.mk fun u => ((u.val : (A ⧸ I)ˣ) : A ⧸ I) • untw ρ χ hχ I m
      map_zero' := TwFun.ext fun u => by
        rw [TwFun.val_mk, TwFun.val_zero, untw_zero, smul_zero]
      map_add' := fun m m' => TwFun.ext fun u => by
        rw [TwFun.val_mk, TwFun.val_add, TwFun.val_mk, TwFun.val_mk, untw_add, smul_add] }
  have hι_val : ∀ (m : W) (u : Idx χb),
      (ι m).val u = ((u.val : (A ⧸ I)ˣ) : A ⧸ I) • untw ρ χ hχ I m := fun m u => rfl
  have hι_inj : Function.Injective ι := by
    intro m m' h
    have h1 := congrArg (fun φ : TwFun (Idx χb) (Lvl ρ I) => φ.val (Idx.mk χb 1)) h
    simp only [hι_val, Idx.val_mk, Units.val_one, one_smul] at h1
    exact untw_injective ρ χ hχ I h1
  have hι_eq : ∀ (σ : Γℚ) (m : W), ι (σ • m) = σ • ι m := by
    intro σ m
    refine TwFun.ext fun u => ?_
    rw [hι_val, TwFun.val_smul, hι_val, Idx.val_smul, map_inv, inv_inv, Units.val_mul,
      mul_smul, lvl_smul_smul_comm', hχb_coe, lvl_mk_smul, untw_smul, lvl_smul_smul_comm]

  obtain ⟨H, _, _, hHfin, hHflat, hHcomm, e', he'_add, he'_act⟩ :=
    GaloisRep.exists_finiteFlat_sub_of_equivariant_injection p H₁ e₂ he₂_add he₂_act ι hι_inj hι_eq
  exact ⟨H, _, _, hHfin, hHflat, hHcomm, e', he'_add, fun σ f g hfg => he'_act σ f g hfg⟩

end S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one
end P2MW
export P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one (solution)
