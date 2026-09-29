-- Prove2me | solution 1 for GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f65b0c3d-7d1d-546f-8c12-2c2d3e2d6db0

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Theorems.Thm_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr
import Theorems.Thm_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure
import Theorems.Thm_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt

set_option autoImplicit false

namespace P2mUnrFlat

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

def Lvl.mk (ρ : GaloisRepAdic A) (I : Ideal A) (v : ρ.V) : Lvl ρ I := Submodule.Quotient.mk v

theorem Lvl.mk_surjective (ρ : GaloisRepAdic A) (I : Ideal A) : Function.Surjective (Lvl.mk ρ I) :=
  Submodule.Quotient.mk_surjective _

noncomputable scoped instance levelDistribMulAction (ρ : GaloisRepAdic A) (I : Ideal A) :
    DistribMulAction Γℚ (Lvl ρ I) where
  smul σ m := ρ.levelAction I σ m
  one_smul m := by
    obtain ⟨v, rfl⟩ := Lvl.mk_surjective ρ I m
    change ρ.levelAction I 1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    rw [levelAction_mk, map_one, Module.End.one_apply]
  mul_smul σ τ m := by
    obtain ⟨v, rfl⟩ := Lvl.mk_surjective ρ I m
    change ρ.levelAction I (σ * τ) (Submodule.Quotient.mk v) =
      ρ.levelAction I σ (ρ.levelAction I τ (Submodule.Quotient.mk v))
    rw [levelAction_mk, levelAction_mk, levelAction_mk, map_mul, Module.End.mul_apply]
  smul_zero σ := map_zero (ρ.levelAction I σ)
  smul_add σ x y := map_add (ρ.levelAction I σ) x y

theorem lvl_smul_def (ρ : GaloisRepAdic A) (I : Ideal A) (σ : Γℚ) (m : Lvl ρ I) :
    σ • m = ρ.levelAction I σ m := rfl

theorem lvl_smul_mk (ρ : GaloisRepAdic A) (I : Ideal A) (σ : Γℚ) (v : ρ.V) :
    σ • Lvl.mk ρ I v = Lvl.mk ρ I (ρ.ρ σ v) := rfl

theorem lvl_smul_eq_of_apply_eq_one (ρ : GaloisRepAdic A) (I : Ideal A) {σ : Γℚ}
    (hσ : ρ.ρ σ = 1) (m : Lvl ρ I) : σ • m = m := by
  obtain ⟨v, rfl⟩ := Lvl.mk_surjective ρ I m
  rw [lvl_smul_mk, hσ, Module.End.one_apply]

end level

def Triv (N : Type) : Type := N

def Triv.mk {N : Type} (x : N) : Triv N := x

def Triv.val {N : Type} (x : Triv N) : N := x

@[scoped simp] theorem Triv.val_mk {N : Type} (x : N) : (Triv.mk x).val = x := rfl
p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.Triv"
@[scoped simp] theorem Triv.mk_val {N : Type} (x : Triv N) : Triv.mk x.val = x := rfl

p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.Triv"
theorem Triv.mk_injective {N : Type} : Function.Injective (Triv.mk : N → Triv N) := fun _ _ h => h

scoped instance (N : Type) [AddCommGroup N] : AddCommGroup (Triv N) := inferInstanceAs (AddCommGroup N)

scoped instance (N : Type) [Finite N] : Finite (Triv N) := inferInstanceAs (Finite N)

theorem Triv.mk_add {N : Type} [AddCommGroup N] (x y : N) : Triv.mk (x + y) = Triv.mk x + Triv.mk y :=
  rfl

theorem Triv.mk_zero {N : Type} [AddCommGroup N] : Triv.mk (0 : N) = 0 := rfl

scoped instance trivDistribMulAction (N : Type) [AddCommGroup N] : DistribMulAction Γℚ (Triv N) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

theorem Triv.smul_def {N : Type} [AddCommGroup N] (σ : Γℚ) (x : Triv N) : σ • x = x := rfl

theorem algEquiv_algebraMap (p : ℕ) (σ : Γℚ) (r : GaloisRep.ratLocalizedAt p) :
    σ (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r) =
      algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r :=
  σ.commutes (r : ℚ)

theorem exists_constant_model (p : ℕ) (hp : p.Prime) (N : Type) [AddCommGroup N] [Finite N] :
    ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) G),
      Module.Finite (GaloisRep.ratLocalizedAt p) G ∧ Module.Flat (GaloisRep.ratLocalizedAt p) G ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G ∧
      ∃ e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ Triv N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γℚ) (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : G, g x = σ (f x)) → e g = σ • (e f) := by
  classical

  let R : Type := GaloisRep.ratLocalizedAt p
  let X : Type := Triv N
  haveI : Fintype X := Fintype.ofFinite X
  let φ : (X → R) →ₐ[R] (X → AlgebraicClosure ℚ) :=
    AlgHom.compLeft (Algebra.ofId R (AlgebraicClosure ℚ)) X
  have hφ : ∀ (F₀ : X → R) (x : X), φ F₀ x = algebraMap R (AlgebraicClosure ℚ) (F₀ x) :=
    fun _ _ => rfl
  let B : Subalgebra R (X → AlgebraicClosure ℚ) := φ.range
  have hmemB : ∀ F₀ : X → R, φ F₀ ∈ B := fun F₀ => (AlgHom.mem_range φ).mpr ⟨F₀, rfl⟩

  let δ : X → X → R := fun a x => if x = a then 1 else 0
  have hδ : ∀ a x, φ (δ a) x = if x = a then 1 else 0 := by
    intro a x
    rw [hφ]
    change algebraMap R (AlgebraicClosure ℚ) (if x = a then 1 else 0) = _
    split_ifs <;> simp

  refine GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure p hp B ?_ ?_ ?_ ?_ ?_
  ·
    have hB : Subalgebra.toSubmodule B = LinearMap.range φ.toLinearMap := by
      ext F
      simp only [Subalgebra.mem_toSubmodule, LinearMap.mem_range, AlgHom.toLinearMap_apply, B,
        AlgHom.mem_range]
    rw [hB, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top (R := R) (M := X → R)).map _
  ·
    intro F hF σ x
    obtain ⟨F₀, rfl⟩ := (AlgHom.mem_range φ).mp hF
    rw [Triv.smul_def, hφ, algEquiv_algebraMap]
  ·
    intro F hF
    obtain ⟨F₀, rfl⟩ := (AlgHom.mem_range φ).mp hF
    let eX : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
    refine ⟨Fintype.card X, fun i => φ (δ (eX.symm i)), fun i => φ (fun y => F₀ (eX.symm i + y)),
      fun i => hmemB _, fun i => hmemB _, fun x y => ?_⟩
    have hre : (∑ i : Fin (Fintype.card X), φ (δ (eX.symm i)) x * φ (fun y => F₀ (eX.symm i + y)) y) =
        ∑ a : X, φ (δ a) x * φ (fun y => F₀ (a + y)) y :=
      Equiv.sum_comp eX.symm (fun a : X => φ (δ a) x * φ (fun y => F₀ (a + y)) y)
    rw [hre]
    simp only [hδ, hφ, boole_mul]
    rw [Finset.sum_ite_eq Finset.univ x (fun a : X => algebraMap R (AlgebraicClosure ℚ) (F₀ (a + y)))]
    simp
  ·
    intro F hF
    obtain ⟨F₀, rfl⟩ := (AlgHom.mem_range φ).mp hF
    exact (AlgHom.mem_range φ).mpr ⟨fun x => F₀ (-x), rfl⟩
  ·
    intro x y hxy
    by_contra hne
    have h1 := hxy (φ (δ x)) (hmemB _)
    rw [hδ, hδ, if_pos rfl, if_neg (Ne.symm hne)] at h1
    exact one_ne_zero h1

def TwFun (S N : Type) : Type := S → N

scoped instance (S N : Type) [AddCommGroup N] : AddCommGroup (TwFun S N) :=
  inferInstanceAs (AddCommGroup (S → N))

def TwFun.val {S N : Type} (φ : TwFun S N) : S → N := φ

def TwFun.mk {S N : Type} (φ : S → N) : TwFun S N := φ

@[scoped simp] theorem TwFun.val_mk {S N : Type} (φ : S → N) : (TwFun.mk φ).val = φ := rfl
p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.Triv P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.TwFun"
@[scoped simp] theorem TwFun.mk_val {S N : Type} (φ : TwFun S N) : TwFun.mk φ.val = φ := rfl

p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.Triv P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.TwFun"
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

theorem main {k : Type} [Field k] [Finite k] (ρ : ResidualGaloisRep k) {p : ℕ} (hp : p.Prime)
    (h : (GaloisRepAdic.ofResidualGaloisRep ρ).IsUnramifiedAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p := by
  classical
  set ρA : GaloisRepAdic k := GaloisRepAdic.ofResidualGaloisRep ρ with hρA
  refine ⟨Finite.of_surjective _ (IsLocalRing.residue_surjective (R := k)), fun I hI => ?_⟩
  haveI := hI

  haveI hVfin : Finite ρA.V := Module.finite_of_finite k
  haveI hLfin : Finite (Lvl ρA I) := Finite.of_surjective _ (Lvl.mk_surjective ρA I)

  let ρu : Γℚ →* (Module.End k ρA.V)ˣ := ρA.ρ.toHomUnits
  have hρu : ∀ σ : Γℚ, σ ∈ ρu.ker ↔ ρA.ρ σ = 1 := fun σ => by
    rw [MonoidHom.mem_ker, ← Units.val_eq_one, MonoidHom.coe_toHomUnits]
  set Δ : Subgroup Γℚ := ρu.ker with hΔdef
  haveI hΔn : Δ.Normal := MonoidHom.normal_ker ρu

  obtain ⟨L, hLfd, hL⟩ := ρ.factorsThroughFiniteLevel
  haveI := hLfd
  have hLΔ : L.fixingSubgroup ≤ Δ := fun σ hσ =>
    (hρu σ).mpr (hL σ fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ x hx)
  have hopen : IsOpen (Δ : Set Γℚ) := Subgroup.isOpen_mono hLΔ L.fixingSubgroup_isOpen
  have hclosed : IsClosed (Δ : Set Γℚ) := Subgroup.isClosed_of_isOpen _ hopen

  set K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField Δ with hKdef
  have hfix : K.fixingSubgroup = Δ :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨Δ, hclosed⟩
  haveI hKfin : FiniteDimensional ℚ K :=
    (InfiniteGalois.isOpen_iff_finite K).mp (by rw [hfix]; exact hopen)
  haveI hKgal : IsGalois ℚ K :=
    (InfiniteGalois.normal_iff_isGalois K).mp (by rw [hfix]; infer_instance)
  have hKΔ : ∀ σ : Γℚ, (∀ x ∈ K, σ x = x) → σ ∈ Δ := fun σ hσ =>
    hfix ▸ (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ

  have hdisc := IntermediateField.not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup K p hp
    (fun P hP σ hσ => by
      rw [hfix]
      exact (hρu σ).mpr (h P hP σ hσ))

  haveI hSfin : Finite (Γℚ ⧸ Δ) := by
    haveI : Finite (Module.End k ρA.V) :=
      Finite.of_injective (fun f : Module.End k ρA.V => (f : ρA.V → ρA.V))
        (fun _ _ hfg => LinearMap.ext (congrFun hfg))
    haveI : Finite (Module.End k ρA.V)ˣ := Finite.of_injective _ Units.val_injective
    exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρu).symm.toEquiv
  have hS : ∀ σ : Γℚ, (∀ x ∈ K, σ x = x) → ∀ s : Γℚ ⧸ Δ, σ • s = s := by
    intro σ hσ s
    induction s using QuotientGroup.induction_on with
    | H τ =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      have hmem : τ⁻¹ * σ⁻¹ * τ⁻¹⁻¹ ∈ Δ := hΔn.conj_mem _ (inv_mem (hKΔ σ hσ)) τ⁻¹
      simpa only [inv_inv, mul_inv_rev, mul_assoc] using hmem

  obtain ⟨G, _, _, hGfin, hGflat, hGcomm, e, he_add, he_act⟩ :=
    exists_constant_model p hp (Lvl ρA I)
  haveI := hGfin
  haveI := hGflat
  haveI := hGcomm

  obtain ⟨H₁, _, _, h₁fin, h₁flat, h₁comm, e₁, he₁_add, he₁_act⟩ :=
    GaloisRep.exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr p hp G (M := Triv (Lvl ρA I))
      e he_add (fun σ f g hfg => he_act σ f g hfg) (S := Γℚ ⧸ Δ) K hdisc hS
  haveI := h₁fin
  haveI := h₁flat
  haveI := h₁comm

  let e₂ : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      TwFun (Γℚ ⧸ Δ) (Triv (Lvl ρA I)) := e₁.trans ⟨TwFun.mk, TwFun.val, fun _ => rfl, fun _ => rfl⟩
  have he₂_val : ∀ f, (e₂ f).val = e₁ f := fun f => rfl
  have he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g := fun f g =>
    TwFun.ext fun s => by rw [TwFun.val_add, he₂_val, he₂_val, he₂_val, he₁_add]; rfl
  have he₂_act : ∀ (σ : Γℚ) (f g : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H₁, g x = σ (f x)) → e₂ g = σ • e₂ f := fun σ f g hfg =>
    TwFun.ext fun s => by rw [TwFun.val_smul, he₂_val, he₂_val, he₁_act σ f g hfg]

  have hΔ_smul : ∀ κ ∈ Δ, ∀ m : Lvl ρA I, κ • m = m := fun κ hκ m =>
    lvl_smul_eq_of_apply_eq_one ρA I ((hρu κ).mp hκ) m
  let ιf : Lvl ρA I → Γℚ ⧸ Δ → Triv (Lvl ρA I) := fun m s =>
    Quotient.liftOn' s (fun τ : Γℚ => Triv.mk (τ⁻¹ • m)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      change Triv.mk (a⁻¹ • m) = Triv.mk (b⁻¹ • m)
      have hb : b⁻¹ = (a⁻¹ * b)⁻¹ * a⁻¹ := by group
      rw [hb, mul_smul, hΔ_smul _ (inv_mem hab)])
  have hιf_mk : ∀ (m : Lvl ρA I) (τ : Γℚ), ιf m (QuotientGroup.mk τ) = Triv.mk (τ⁻¹ • m) :=
    fun _ _ => rfl
  let ι : Lvl ρA I →+ TwFun (Γℚ ⧸ Δ) (Triv (Lvl ρA I)) :=
    { toFun := fun m => TwFun.mk (ιf m)
      map_zero' := TwFun.ext fun s => by
        induction s using QuotientGroup.induction_on with
        | H τ => rw [TwFun.val_mk, hιf_mk, TwFun.val_zero, smul_zero, Triv.mk_zero]
      map_add' := fun m m' => TwFun.ext fun s => by
        induction s using QuotientGroup.induction_on with
        | H τ => rw [TwFun.val_add, TwFun.val_mk, TwFun.val_mk, TwFun.val_mk, hιf_mk, hιf_mk,
            hιf_mk, smul_add, Triv.mk_add] }
  have hι_val : ∀ (m : Lvl ρA I) (τ : Γℚ), (ι m).val (QuotientGroup.mk τ) = Triv.mk (τ⁻¹ • m) :=
    fun _ _ => rfl
  have hι_inj : Function.Injective ι := by
    intro m m' hmm
    have h1 := congrArg (fun ψ : TwFun (Γℚ ⧸ Δ) (Triv (Lvl ρA I)) => ψ.val (QuotientGroup.mk 1)) hmm
    simp only [hι_val, inv_one, one_smul] at h1
    exact Triv.mk_injective h1
  have hι_eq : ∀ (σ : Γℚ) (m : Lvl ρA I), ι (σ • m) = σ • ι m := by
    intro σ m
    refine TwFun.ext fun s => ?_
    induction s using QuotientGroup.induction_on with
    | H τ =>
      rw [TwFun.val_smul, Triv.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, hι_val, hι_val,
        mul_inv_rev, inv_inv, mul_smul]

  obtain ⟨H, _, _, hHfin, hHflat, hHcomm, e', he'_add, he'_act⟩ :=
    GaloisRep.exists_finiteFlat_sub_of_equivariant_injection p H₁ e₂ he₂_add he₂_act ι hι_inj hι_eq
  exact ⟨H, _, _, hHfin, hHflat, hHcomm, e', he'_add, fun σ f g hfg => he'_act σ f g hfg⟩

end P2mUnrFlat
p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.Triv P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.TwFun P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat"

theorem solution
    {k : Type} [Field k] [Finite k] (ρ : ResidualGaloisRep k) {p : ℕ} (hp : p.Prime)
    (h : (GaloisRepAdic.ofResidualGaloisRep ρ).IsUnramifiedAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p :=
  P2mUnrFlat.main ρ hp h

end S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt
end P2MW
export P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt (solution)
