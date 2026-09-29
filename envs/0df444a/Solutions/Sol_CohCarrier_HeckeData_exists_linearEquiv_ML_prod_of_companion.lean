-- Prove2me | solution 1 for CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/98374b1a-203c-5756-ad9a-a13a279c3587

import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import Theorems.Thm_CohCarrier_HeckeData_finite_ML_and_free_ML
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion
p2m_attr_erase "instance" "IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing"
p2m_attr_erase "simp" "IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

noncomputable section

open CohCarrier IsLocalRing

namespace TWCompanion

section Residue
variable {𝒪 : Type} [CommRing 𝒪] {V : Type} [AddCommGroup V] [Module 𝒪 V]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

abbrev Loc : Type := Localization D.mTheta.primeCompl

theorem thetaTilde_ne_zero_of_mem (s : D.mTheta.primeCompl) : D.thetaTilde (s : D.FreeAlg) ≠ 0 :=
  fun h => s.2 (by
    show (s : D.FreeAlg) ∈ RingHom.ker D.thetaTilde.toRingHom
    exact h)

theorem mem_primeCompl_iff (f : D.FreeAlg) : f ∈ D.mTheta.primeCompl ↔ D.thetaTilde f ≠ 0 := by
  show f ∉ RingHom.ker D.thetaTilde.toRingHom ↔ _
  rw [RingHom.mem_ker]
  rfl

def Θ : Loc D →+* k :=
  IsLocalization.lift (M := D.mTheta.primeCompl) (g := D.thetaTilde.toRingHom)
    (fun s => isUnit_iff_ne_zero.mpr (thetaTilde_ne_zero_of_mem D s))

@[scoped simp] theorem Θ_algebraMap (f : D.FreeAlg) : Θ D (algebraMap D.FreeAlg (Loc D) f) = D.thetaTilde f :=
  IsLocalization.lift_eq _ f

theorem Θ_algebraMap_base (a : 𝒪) : Θ D (algebraMap 𝒪 (Loc D) a) = algebraMap 𝒪 k a := by
  rw [IsScalarTower.algebraMap_apply 𝒪 D.FreeAlg (Loc D), Θ_algebraMap, AlgHom.commutes]

theorem Θ_X (g : D.Gen) : Θ D (algebraMap D.FreeAlg (Loc D) (MvPolynomial.X g)) = D.θbar g := by
  rw [Θ_algebraMap]
  show MvPolynomial.aeval D.θbar (MvPolynomial.X g) = D.θbar g
  exact MvPolynomial.aeval_X _ g

theorem isUnit_iff_Θ_ne_zero (z : Loc D) : IsUnit z ↔ Θ D z ≠ 0 := by
  constructor
  · intro hz h0
    exact not_isUnit_zero (h0 ▸ hz.map (Θ D))
  · intro hz
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective D.mTheta.primeCompl z
    apply (IsLocalization.AtPrime.isUnit_mk'_iff (Loc D) D.mTheta f s).mpr
    rw [mem_primeCompl_iff]
    intro hf
    apply hz
    show Θ D (IsLocalization.mk' (Loc D) f s) = 0
    rw [Θ, IsLocalization.lift_mk'_spec]
    show D.thetaTilde f = D.thetaTilde s * 0
    rw [hf, mul_zero]

theorem isUnit_algebraMap_of_ne (f : D.FreeAlg) (hf : D.thetaTilde f ≠ 0) :
    IsUnit (algebraMap D.FreeAlg (Loc D) f) :=
  (isUnit_iff_Θ_ne_zero D _).mpr (by rwa [Θ_algebraMap])

theorem mem_maximalIdeal_iff_Θ_eq_zero (z : Loc D) : z ∈ maximalIdeal (Loc D) ↔ Θ D z = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_Θ_ne_zero, not_not]
end Residue

section LocMod
variable {R : Type} [CommRing R] {S : Submonoid R} {M : Type} [AddCommGroup M] [Module R M]

theorem mk_eq_zero_iff (m : M) (s : S) :
    LocalizedModule.mk m s = 0 ↔ ∃ u : S, (u : R) • m = 0 := by
  rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
  simp only [smul_zero, Submonoid.smul_def]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u * s, by rw [Submonoid.coe_mul, mul_smul]; exact hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [smul_comm, hu, smul_zero]⟩

theorem isUnit_smul_loc (s : S) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule S M)) s) :=
  IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M) s

theorem smul_loc_injective (s : S) {x y : LocalizedModule S M} (h : (s : R) • x = (s : R) • y) :
    x = y :=
  (Module.End.isUnit_iff _).mp (isUnit_smul_loc (M := M) s) |>.1 h
end LocMod

section CompanionOp
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

private def _root_.TWCompanion.comp (T Dinv : Module.End R M) (c : R) : Module.End R (M × M) :=
  (T ∘ₗ LinearMap.fst R M M + c • LinearMap.snd R M M).prod (-(Dinv ∘ₗ LinearMap.fst R M M))

p2m_export "TWCompanion" "comp"
@[scoped simp] private theorem _root_.TWCompanion.comp_apply (T Dinv : Module.End R M) (c : R) (x : M × M) :
    comp T Dinv c x = (T x.1 + c • x.2, -(Dinv x.1)) := rfl

p2m_export "TWCompanion" "comp_apply"

def diag (f : Module.End R M) : Module.End R (M × M) := f.prodMap f

@[scoped simp] theorem diag_apply (f : Module.End R M) (x : M × M) : diag f x = (f x.1, f x.2) := rfl

theorem comp_sq (T Dinv : Module.End R M) (c : R) (h : T * Dinv = Dinv * T) (x : M × M) :
    comp T Dinv c (comp T Dinv c x) = diag T (comp T Dinv c x) - c • diag Dinv x := by
  obtain ⟨x, y⟩ := x
  have h' : T (Dinv x) = Dinv (T x) := congrArg (fun f : Module.End R M => f x) h
  ext <;> simp [map_add, map_smul, map_neg, h'] <;> abel

theorem diag_comp_comm (T Dinv f : Module.End R M) (c : R) (hT : f * T = T * f)
    (hD : f * Dinv = Dinv * f) : diag f * comp T Dinv c = comp T Dinv c * diag f := by
  have hT' : ∀ v, f (T v) = T (f v) := fun v => congrArg (fun g : Module.End R M => g v) hT
  have hD' : ∀ v, f (Dinv v) = Dinv (f v) := fun v => congrArg (fun g : Module.End R M => g v) hD
  apply LinearMap.ext
  rintro ⟨x, y⟩
  ext <;> simp [map_add, map_smul, map_neg, hT', hD']
end CompanionOp

section SemiLift
variable {A : Type} [CommRing A]
  {R : Type} [CommRing R] [Algebra A R] (S : Submonoid R)
  {M : Type} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
  {B : Type} [CommRing B] [Algebra A B]
  {N : Type} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (ψ : R →ₐ[A] B) (κ : M →ₗ[A] N) (hκ : ∀ (r : R) (m : M), κ (r • m) = ψ r • κ m)
  (hS : ∀ s : S, IsUnit (ψ (s : R)))

def uinv (s : S) : B := ↑((hS s).unit⁻¹)

theorem uinv_mul (s : S) : uinv S ψ hS s * ψ (s : R) = 1 := (hS s).val_inv_mul

theorem mul_uinv (s : S) : ψ (s : R) * uinv S ψ hS s = 1 := (hS s).mul_val_inv

theorem uinv_mul_apply (s : S) (n : N) : uinv S ψ hS s • ψ (s : R) • n = n := by
  rw [← mul_smul, uinv_mul, one_smul]

theorem uinv_mulS (s t : S) : uinv S ψ hS (s * t) = uinv S ψ hS s * uinv S ψ hS t := by
  have h1 : uinv S ψ hS (s * t) * (ψ (s : R) * ψ (t : R)) = 1 := by
    rw [← map_mul, ← Submonoid.coe_mul]; exact uinv_mul S ψ hS (s * t)
  calc uinv S ψ hS (s * t)
      = uinv S ψ hS (s * t) * (ψ (s : R) * ψ (t : R)) * (uinv S ψ hS s * uinv S ψ hS t) := by
          rw [mul_assoc, show ψ (s : R) * ψ (t : R) * (uinv S ψ hS s * uinv S ψ hS t) = 1 by
            calc _ = (ψ (s : R) * uinv S ψ hS s) * (ψ (t : R) * uinv S ψ hS t) := by ring
              _ = 1 := by rw [mul_uinv, mul_uinv, one_mul], mul_one]
    _ = _ := by rw [h1, one_mul]

include hκ in

theorem semiLift_wd (p p' : M × S) (h : p ≈ p') :
    uinv S ψ hS p.2 • κ p.1 = uinv S ψ hS p'.2 • κ p'.1 := by
  obtain ⟨m, s⟩ := p
  obtain ⟨m', s'⟩ := p'
  obtain ⟨u, hu⟩ := h

  have hu' : ψ (u : R) • ψ (s' : R) • κ m = ψ (u : R) • ψ (s : R) • κ m' := by
    have := congrArg κ hu
    simp only [Submonoid.smul_def, hκ] at this
    exact this
  have h2 : ψ (s' : R) • κ m = ψ (s : R) • κ m' := by
    have := congrArg (fun n => uinv S ψ hS u • n) hu'
    simp only [uinv_mul_apply] at this
    exact this
  show uinv S ψ hS s • κ m = uinv S ψ hS s' • κ m'
  calc uinv S ψ hS s • κ m
      = uinv S ψ hS s • uinv S ψ hS s' • ψ (s' : R) • κ m := by rw [uinv_mul_apply]
    _ = uinv S ψ hS s • uinv S ψ hS s' • ψ (s : R) • κ m' := by rw [h2]
    _ = uinv S ψ hS s' • (uinv S ψ hS s • ψ (s : R) • κ m') := by rw [smul_comm]
    _ = uinv S ψ hS s' • κ m' := by rw [uinv_mul_apply]

def semiLift : LocalizedModule S M →ₗ[A] N where
  toFun x := x.liftOn (fun p => uinv S ψ hS p.2 • κ p.1) (semiLift_wd S ψ κ hκ hS)
  map_add' x y := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      induction y using LocalizedModule.induction_on with
      | h m' s' =>
        rw [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk,
          LocalizedModule.liftOn_mk]
        simp only [map_add, Submonoid.smul_def, hκ, smul_add, uinv_mulS]
        congr 1
        · rw [mul_smul, uinv_mul_apply]
        · rw [mul_smul, smul_comm (uinv S ψ hS s') (ψ (s : R)), uinv_mul_apply]
  map_smul' a x := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      have : a • LocalizedModule.mk m s = LocalizedModule.mk (a • m) s := by
        rw [← IsScalarTower.algebraMap_smul R a (LocalizedModule.mk m s), LocalizedModule.smul'_mk,
          algebraMap_smul]
      rw [this, LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk, RingHom.id_apply, map_smul,
        smul_comm]

theorem semiLift_mk (m : M) (s : S) :
    semiLift S ψ κ hκ hS (LocalizedModule.mk m s) = uinv S ψ hS s • κ m := by
  simp only [semiLift, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LocalizedModule.liftOn_mk]

theorem semiLift_mk_one (m : M) : semiLift S ψ κ hκ hS (LocalizedModule.mk m 1) = κ m := by
  rw [semiLift_mk]
  have : uinv S ψ hS 1 = 1 := by
    have h := uinv_mul S ψ hS 1
    rwa [OneMemClass.coe_one, map_one, mul_one] at h
  rw [this, one_smul]

theorem semiLift_smul (r : R) (x : LocalizedModule S M) :
    semiLift S ψ κ hκ hS (r • x) = ψ r • semiLift S ψ κ hκ hS x := by
  induction x using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.smul'_mk, semiLift_mk, semiLift_mk, hκ, smul_comm]

theorem semiLift_mk'_smul (r : R) (s : S) (x : LocalizedModule S M) :
    semiLift S ψ κ hκ hS (IsLocalization.mk' (Localization S) r s • x) =
      (ψ r * uinv S ψ hS s) • semiLift S ψ κ hκ hS x := by
  have hsx : (s : R) • (IsLocalization.mk' (Localization S) r s • x) = r • x := by
    rw [← IsScalarTower.algebraMap_smul (Localization S) (s : R), ← mul_smul,
      IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
      IsScalarTower.algebraMap_smul]
  have := congrArg (semiLift S ψ κ hκ hS) hsx
  rw [semiLift_smul, semiLift_smul] at this
  calc semiLift S ψ κ hκ hS (IsLocalization.mk' (Localization S) r s • x)
      = uinv S ψ hS s • ψ (s : R) • semiLift S ψ κ hκ hS (IsLocalization.mk' (Localization S) r s • x) :=
        (uinv_mul_apply S ψ hS s _).symm
    _ = uinv S ψ hS s • ψ r • semiLift S ψ κ hκ hS x := by rw [this]
    _ = _ := by rw [← mul_smul, mul_comm]
end SemiLift

section Residue2
variable {𝒪 : Type} [CommRing 𝒪] {V : Type} [AddCommGroup V] [Module 𝒪 V]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

def ΘA : Loc D →ₐ[𝒪] k :=
  { Θ D with commutes' := fun a => Θ_algebraMap_base D a }

@[scoped simp] theorem ΘA_apply (z : Loc D) : ΘA D z = Θ D z := rfl

theorem Θ_inverse {z : Loc D} (hz : IsUnit z) : Θ D (Ring.inverse z) = (Θ D z)⁻¹ := by
  have h1 : Θ D z * Θ D (Ring.inverse z) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hz, map_one]
  have hz0 : Θ D z ≠ 0 := (isUnit_iff_Θ_ne_zero D z).mp hz
  field_simp
  rw [mul_comm]; exact h1

theorem algebraMap_smul_ML (f : D.FreeAlg) (x : D.ML) :
    algebraMap D.FreeAlg (Loc D) f • x = f • x :=
  IsScalarTower.algebraMap_smul (Loc D) f x

theorem X_smul_mk (g : D.Gen) (v : V) (s : D.mTheta.primeCompl) :
    (MvPolynomial.X g : D.FreeAlg) • LocalizedModule.mk v s = LocalizedModule.mk (D.op g v) s := by
  rw [LocalizedModule.smul'_mk]
  congr 1
  show D.opAlgHom (MvPolynomial.X g) v = D.op g v
  rw [HeckeData.opAlgHom_X]

theorem X_smul_raw (g : D.Gen) (v : V) : (MvPolynomial.X g : D.FreeAlg) • v = D.op g v := by
  show D.opAlgHom (MvPolynomial.X g) v = D.op g v
  rw [HeckeData.opAlgHom_X]

theorem smul_injective_of_isUnit {z : Loc D} (hz : IsUnit z) {x y : D.ML} (h : z • x = z • y) :
    x = y := by
  have := congrArg (fun w => Ring.inverse z • w) h
  simp only [← mul_smul, Ring.inverse_mul_cancel _ hz, one_smul] at this
  exact this

theorem isUnit_algebraMap_X {g : D.Gen} (hg : D.θbar g ≠ 0) :
    IsUnit (algebraMap D.FreeAlg (Loc D) (MvPolynomial.X g)) :=
  (isUnit_iff_Θ_ne_zero D _).mpr (by rwa [Θ_X])
end Residue2

section Setting
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V : Type} [AddCommGroup V] [Module 𝒪 V]
  (DV : HeckeData 𝒪 V k) (DP : HeckeData 𝒪 (V × V) k)
  {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σP : G ⊕ Unit ≃ DP.Gen) (c : 𝒪) (d : G)

def uHat : Loc DP := algebraMap DP.FreeAlg (Loc DP) (MvPolynomial.X (σP (Sum.inr ())))

def dHat : Loc DP := algebraMap DP.FreeAlg (Loc DP) (MvPolynomial.X (σP (Sum.inl d)))

def ψτ : Loc DP := uHat DP σP + algebraMap 𝒪 (Loc DP) c * (Ring.inverse (dHat DP σP d) *
  Ring.inverse (uHat DP σP))

def ψ : DV.FreeAlg →ₐ[𝒪] Loc DP :=
  MvPolynomial.aeval fun γ => Sum.elim
    (fun g => algebraMap DP.FreeAlg (Loc DP) (MvPolynomial.X (σP (Sum.inl g))))
    (fun _ => ψτ DP σP c d) (σV.symm γ)

theorem ψ_X_inl (g : G) :
    ψ DV DP σV σP c d (MvPolynomial.X (σV (Sum.inl g))) =
      algebraMap DP.FreeAlg (Loc DP) (MvPolynomial.X (σP (Sum.inl g))) := by
  rw [ψ, MvPolynomial.aeval_X, Equiv.symm_apply_apply]; rfl

theorem ψ_X_inr :
    ψ DV DP σV σP c d (MvPolynomial.X (σV (Sum.inr ()))) = ψτ DP σP c d := by
  rw [ψ, MvPolynomial.aeval_X, Equiv.symm_apply_apply]; rfl

section ResidualData
variable (α β : k)
  (hθ : ∀ g : G, DP.θbar (σP (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))
  (hα : DP.θbar (σP (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
  (hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k c) (hc : algebraMap 𝒪 k c ≠ 0)

include hprod hc in
theorem α_ne_zero : α ≠ 0 := by
  rintro rfl; apply hc; rw [← hprod]; ring

include hprod hc in
theorem δ_ne_zero : DV.θbar (σV (Sum.inl d)) ≠ 0 := by
  intro h; apply hc; rw [← hprod, h]; ring

include hα hprod hc in
theorem isUnit_uHat : IsUnit (uHat DP σP) :=
  isUnit_algebraMap_X DP (by rw [hα]; exact α_ne_zero DV σV c d α β hprod hc)

include hθ hprod hc in
theorem isUnit_dHat : IsUnit (dHat DP σP d) :=
  isUnit_algebraMap_X DP (by rw [hθ]; exact δ_ne_zero DV σV c d α β hprod hc)

include hθ hα hprod hc in
theorem Θ_ψτ : Θ DP (ψτ DP σP c d) = α + β := by
  have hα0 := α_ne_zero DV σV c d α β hprod hc
  have hδ0 := δ_ne_zero DV σV c d α β hprod hc
  rw [ψτ, map_add, map_mul, map_mul, Θ_inverse DP (isUnit_uHat DV DP σV σP c d α β hα hprod hc),
    Θ_inverse DP (isUnit_dHat DV DP σV σP c d α β hθ hprod hc), uHat, dHat, Θ_X, Θ_X, hα, hθ,
    Θ_algebraMap_base, ← hprod]
  field_simp

include hθ hα hT hprod hc in

theorem Θ_ψ (f : DV.FreeAlg) : Θ DP (ψ DV DP σV σP c d f) = DV.thetaTilde f := by
  suffices h : (ΘA DP).comp (ψ DV DP σV σP c d) = DV.thetaTilde from
    congrArg (fun φ : DV.FreeAlg →ₐ[𝒪] k => φ f) h
  apply MvPolynomial.algHom_ext
  intro γ
  obtain ⟨x, rfl⟩ := σV.surjective γ
  show Θ DP (ψ DV DP σV σP c d (MvPolynomial.X (σV x))) = MvPolynomial.aeval DV.θbar (MvPolynomial.X (σV x))
  rw [MvPolynomial.aeval_X]
  rcases x with g | u
  · rw [ψ_X_inl, Θ_X, hθ]
  · obtain rfl : u = () := rfl
    rw [ψ_X_inr, Θ_ψτ DV DP σV σP c d α β hθ hα hprod hc, hT]

include hθ hα hT hprod hc in

theorem isUnit_ψ (s : DV.mTheta.primeCompl) : IsUnit (ψ DV DP σV σP c d (s : DV.FreeAlg)) := by
  rw [isUnit_iff_Θ_ne_zero, Θ_ψ DV DP σV σP c d α β hθ hα hT hprod hc]
  exact thetaTilde_ne_zero_of_mem DV s
end ResidualData

section Operators
variable (Dinv : Module.End 𝒪 V)
  (hopP_inl : ∀ g : G, DP.op (σP (Sum.inl g)) = diag (DV.op (σV (Sum.inl g))))
  (hopP_inr : DP.op (σP (Sum.inr ())) = comp (DV.op (σV (Sum.inr ()))) Dinv c)
  (hDinv : DV.op (σV (Sum.inl d)) * Dinv = 1) (hDinv' : Dinv * DV.op (σV (Sum.inl d)) = 1)

theorem comm_of_comm_inv {R : Type} [Ring R] {f D Di : R} (h : f * D = D * f) (h1 : D * Di = 1)
    (h2 : Di * D = 1) : f * Di = Di * f := by
  calc f * Di = (Di * D) * f * Di := by rw [h2, one_mul]
    _ = Di * (D * f) * Di := by rw [mul_assoc Di D f]
    _ = Di * (f * D) * Di := by rw [h]
    _ = Di * f * (D * Di) := by simp only [mul_assoc]
    _ = Di * f := by rw [h1, mul_one]

include hDinv hDinv' in

theorem T_Dinv_comm : DV.op (σV (Sum.inr ())) * Dinv = Dinv * DV.op (σV (Sum.inr ())) :=
  comm_of_comm_inv (DV.comm (σV (Sum.inr ())) (σV (Sum.inl d))) hDinv hDinv'

include hDinv hDinv' in

theorem X_Dinv_comm (g : G) : DV.op (σV (Sum.inl g)) * Dinv = Dinv * DV.op (σV (Sum.inl g)) :=
  comm_of_comm_inv (DV.comm (σV (Sum.inl g)) (σV (Sum.inl d))) hDinv hDinv'

theorem mk_one_add (p p' : V × V) :
    (LocalizedModule.mk (p + p') 1 : DP.ML) = LocalizedModule.mk p 1 + LocalizedModule.mk p' 1 :=
  (LocalizedModule.mkLinearMap DP.mTheta.primeCompl (V × V)).map_add p p'

theorem mk_one_smul (a : 𝒪) (p : V × V) :
    (LocalizedModule.mk (a • p) 1 : DP.ML) = a • LocalizedModule.mk p 1 := by
  rw [← IsScalarTower.algebraMap_smul DP.FreeAlg a (LocalizedModule.mk p 1),
    LocalizedModule.smul'_mk, algebraMap_smul]

theorem mk_one_neg (p : V × V) :
    (LocalizedModule.mk (-p) 1 : DP.ML) = -LocalizedModule.mk p 1 :=
  (LocalizedModule.mkLinearMap DP.mTheta.primeCompl (V × V)).map_neg p

theorem uHat_smul_mk (p : V × V) :
    uHat DP σP • (LocalizedModule.mk p 1 : DP.ML) = LocalizedModule.mk (DP.op (σP (Sum.inr ())) p) 1 := by
  rw [uHat, algebraMap_smul_ML, X_smul_mk]

theorem dHat_smul_mk (p : V × V) :
    dHat DP σP d • (LocalizedModule.mk p 1 : DP.ML) = LocalizedModule.mk (DP.op (σP (Sum.inl d)) p) 1 := by
  rw [dHat, algebraMap_smul_ML, X_smul_mk]

include hopP_inl hopP_inr hDinv hDinv' in

theorem ψτ_smul_mk (hu : IsUnit (uHat DP σP)) (hd : IsUnit (dHat DP σP d)) (p : V × V) :
    ψτ DP σP c d • (LocalizedModule.mk p 1 : DP.ML) =
      LocalizedModule.mk (diag (DV.op (σV (Sum.inr ()))) p) 1 := by
  set T := DV.op (σV (Sum.inr ()))
  set Dop := DV.op (σV (Sum.inl d))
  set u := comp T Dinv c
  have hz : IsUnit (dHat DP σP d * uHat DP σP) := hd.mul hu
  apply smul_injective_of_isUnit DP hz

  have hlhs : dHat DP σP d * uHat DP σP * ψτ DP σP c d =
      dHat DP σP d * uHat DP σP * uHat DP σP + algebraMap 𝒪 (Loc DP) c := by
    rw [ψτ, mul_add]
    congr 1
    calc dHat DP σP d * uHat DP σP * (algebraMap 𝒪 (Loc DP) c *
          (Ring.inverse (dHat DP σP d) * Ring.inverse (uHat DP σP)))
        = algebraMap 𝒪 (Loc DP) c * ((dHat DP σP d * Ring.inverse (dHat DP σP d)) *
            (uHat DP σP * Ring.inverse (uHat DP σP))) := by ring
      _ = algebraMap 𝒪 (Loc DP) c := by
          rw [Ring.mul_inverse_cancel _ hd, Ring.mul_inverse_cancel _ hu, one_mul, mul_one]
  rw [← mul_smul, hlhs, add_smul, mul_smul, mul_smul, uHat_smul_mk, uHat_smul_mk, dHat_smul_mk,
    IsScalarTower.algebraMap_smul, ← mk_one_smul, ← mk_one_add, mul_smul, uHat_smul_mk, dHat_smul_mk,
    hopP_inr, hopP_inl]
  congr 1

  have hTD : T * Dinv = Dinv * T := T_Dinv_comm DV σV d Dinv hDinv hDinv'
  have hcomm : diag T * u = u * diag T := diag_comp_comm T Dinv T c rfl hTD
  rw [comp_sq T Dinv c hTD p, show diag T (u p) = u (diag T p) from
    congrArg (fun f : Module.End 𝒪 (V × V) => f p) hcomm, map_sub, map_smul]
  have hDD : ∀ x : V × V, diag Dop (diag Dinv x) = x := fun x => by
    have h1 : ∀ v, Dop (Dinv v) = v := fun v => congrArg (fun f : Module.End 𝒪 V => f v) hDinv
    ext <;> simp [h1]
  rw [hDD]
  abel

def κ₁ : V →ₗ[𝒪] DP.ML := DP.toMLₒ ∘ₗ LinearMap.inl 𝒪 V V

def κ₂ : V →ₗ[𝒪] DP.ML := DP.toMLₒ ∘ₗ LinearMap.inr 𝒪 V V

theorem κ₁_apply (v : V) : κ₁ DP v = LocalizedModule.mk (v, 0) 1 := rfl

theorem κ₂_apply (v : V) : κ₂ DP v = LocalizedModule.mk (0, v) 1 := rfl

include hopP_inl hopP_inr hDinv hDinv' in

theorem κ₁_smul (hu : IsUnit (uHat DP σP)) (hd : IsUnit (dHat DP σP d)) (f : DV.FreeAlg) (v : V) :
    κ₁ DP (f • v) = ψ DV DP σV σP c d f • κ₁ DP v := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C a =>
    rw [show (MvPolynomial.C a : DV.FreeAlg) = algebraMap 𝒪 DV.FreeAlg a from rfl, algebraMap_smul,
      AlgHom.commutes, IsScalarTower.algebraMap_smul, map_smul]
  | add p q hp hq => rw [add_smul, map_add, hp, hq, map_add, add_smul]
  | mul_X p γ hp =>
    rw [mul_smul, hp, map_mul, mul_smul]
    congr 1
    obtain ⟨x, rfl⟩ := σV.surjective γ
    rcases x with g | u
    · rw [ψ_X_inl, X_smul_raw, κ₁_apply, κ₁_apply, algebraMap_smul_ML, X_smul_mk, hopP_inl]
      simp [diag]
    · obtain rfl : u = () := rfl
      rw [ψ_X_inr, X_smul_raw, κ₁_apply, κ₁_apply,
        ψτ_smul_mk DV DP σV σP c d Dinv hopP_inl hopP_inr hDinv hDinv' hu hd]
      simp [diag]

include hopP_inl hopP_inr hDinv hDinv' in

theorem κ₂_smul (hu : IsUnit (uHat DP σP)) (hd : IsUnit (dHat DP σP d)) (f : DV.FreeAlg) (v : V) :
    κ₂ DP (f • v) = ψ DV DP σV σP c d f • κ₂ DP v := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C a =>
    rw [show (MvPolynomial.C a : DV.FreeAlg) = algebraMap 𝒪 DV.FreeAlg a from rfl, algebraMap_smul,
      AlgHom.commutes, IsScalarTower.algebraMap_smul, map_smul]
  | add p q hp hq => rw [add_smul, map_add, hp, hq, map_add, add_smul]
  | mul_X p γ hp =>
    rw [mul_smul, hp, map_mul, mul_smul]
    congr 1
    obtain ⟨x, rfl⟩ := σV.surjective γ
    rcases x with g | u
    · rw [ψ_X_inl, X_smul_raw, κ₂_apply, κ₂_apply, algebraMap_smul_ML, X_smul_mk, hopP_inl]
      simp [diag]
    · obtain rfl : u = () := rfl
      rw [ψ_X_inr, X_smul_raw, κ₂_apply, κ₂_apply,
        ψτ_smul_mk DV DP σV σP c d Dinv hopP_inl hopP_inr hDinv hDinv' hu hd]
      simp [diag]
end Operators

section Localised

def τHat : Loc DV := algebraMap DV.FreeAlg (Loc DV) (MvPolynomial.X (σV (Sum.inr ())))

def dHatV : Loc DV := algebraMap DV.FreeAlg (Loc DV) (MvPolynomial.X (σV (Sum.inl d)))

def uL : Module.End (Loc DV) (DV.ML × DV.ML) :=
  comp (LinearMap.lsmul (Loc DV) DV.ML (τHat DV σV))
    (LinearMap.lsmul (Loc DV) DV.ML (Ring.inverse (dHatV DV σV d))) (algebraMap 𝒪 (Loc DV) c)

theorem uL_apply (x : DV.ML × DV.ML) :
    uL DV σV c d x = (τHat DV σV • x.1 + algebraMap 𝒪 (Loc DV) c • x.2,
      -(Ring.inverse (dHatV DV σV d) • x.1)) := rfl

variable (α β : k)
  (hθ : ∀ g : G, DP.θbar (σP (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))
  (hα : DP.θbar (σP (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
  (hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k c) (hc : algebraMap 𝒪 k c ≠ 0)
  (Dinv : Module.End 𝒪 V)
  (hopP_inl : ∀ g : G, DP.op (σP (Sum.inl g)) = diag (DV.op (σV (Sum.inl g))))
  (hopP_inr : DP.op (σP (Sum.inr ())) = comp (DV.op (σV (Sum.inr ()))) Dinv c)
  (hDinv : DV.op (σV (Sum.inl d)) * Dinv = 1) (hDinv' : Dinv * DV.op (σV (Sum.inl d)) = 1)

def ν₁ : DV.ML →ₗ[𝒪] DP.ML :=
  semiLift DV.mTheta.primeCompl (ψ DV DP σV σP c d) (κ₁ DP)
    (κ₁_smul DV DP σV σP c d Dinv hopP_inl hopP_inr hDinv hDinv'
      (isUnit_uHat DV DP σV σP c d α β hα hprod hc) (isUnit_dHat DV DP σV σP c d α β hθ hprod hc))
    (isUnit_ψ DV DP σV σP c d α β hθ hα hT hprod hc)

def ν₂ : DV.ML →ₗ[𝒪] DP.ML :=
  semiLift DV.mTheta.primeCompl (ψ DV DP σV σP c d) (κ₂ DP)
    (κ₂_smul DV DP σV σP c d Dinv hopP_inl hopP_inr hDinv hDinv'
      (isUnit_uHat DV DP σV σP c d α β hα hprod hc) (isUnit_dHat DV DP σV σP c d α β hθ hprod hc))
    (isUnit_ψ DV DP σV σP c d α β hθ hα hT hprod hc)

def ν : DV.ML × DV.ML →ₗ[𝒪] DP.ML :=
  ν₁ DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv' ∘ₗ LinearMap.fst _ _ _ +
  ν₂ DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv' ∘ₗ LinearMap.snd _ _ _

def ψL : Loc DV →+* Loc DP :=
  IsLocalization.lift (M := DV.mTheta.primeCompl) (g := (ψ DV DP σV σP c d).toRingHom)
    (isUnit_ψ DV DP σV σP c d α β hθ hα hT hprod hc)

section API
local notation "ν₁♯" => ν₁ DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv'
local notation "ν₂♯" => ν₂ DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv'
local notation "ν♯" => ν DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv'
local notation "ψ♯" => ψ DV DP σV σP c d
local notation "ψL♯" => ψL DV DP σV σP c d α β hθ hα hT hprod hc
local notation "hS♯" => isUnit_ψ DV DP σV σP c d α β hθ hα hT hprod hc

theorem ψL_algebraMap (f : DV.FreeAlg) : ψL♯ (algebraMap DV.FreeAlg (Loc DV) f) = ψ♯ f :=
  IsLocalization.lift_eq _ f

theorem ψL_mk' (f : DV.FreeAlg) (s : DV.mTheta.primeCompl) :
    ψL♯ (IsLocalization.mk' (Loc DV) f s) = ψ♯ f * uinv DV.mTheta.primeCompl (ψ♯) hS♯ s := by
  have h1 : ψL♯ (IsLocalization.mk' (Loc DV) f s) * ψ♯ (s : DV.FreeAlg) = ψ♯ f := by
    rw [← ψL_algebraMap DV DP σV σP c d α β hθ hα hT hprod hc (s : DV.FreeAlg), ← map_mul,
      IsLocalization.mk'_spec, ψL_algebraMap]
  calc ψL♯ (IsLocalization.mk' (Loc DV) f s)
      = ψL♯ (IsLocalization.mk' (Loc DV) f s) * (ψ♯ (s : DV.FreeAlg) *
          uinv DV.mTheta.primeCompl (ψ♯) hS♯ s) := by rw [mul_uinv, mul_one]
    _ = _ := by rw [← mul_assoc, h1]

theorem Θ_ψL (z : Loc DV) : Θ DP (ψL♯ z) = Θ DV z := by
  suffices h : (Θ DP).comp (ψL♯) = Θ DV from RingHom.congr_fun h z
  apply IsLocalization.ringHom_ext DV.mTheta.primeCompl
  refine RingHom.ext fun f => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, ψL_algebraMap, Θ_algebraMap]
  exact Θ_ψ DV DP σV σP c d α β hθ hα hT hprod hc f

theorem ν₁_mk (v : V) (s : DV.mTheta.primeCompl) :
    ν₁♯ (LocalizedModule.mk v s) = uinv DV.mTheta.primeCompl (ψ♯) hS♯ s • κ₁ DP v :=
  semiLift_mk _ _ _ _ _ v s

theorem ν₂_mk (v : V) (s : DV.mTheta.primeCompl) :
    ν₂♯ (LocalizedModule.mk v s) = uinv DV.mTheta.primeCompl (ψ♯) hS♯ s • κ₂ DP v :=
  semiLift_mk _ _ _ _ _ v s

theorem ν_apply (x : DV.ML × DV.ML) : ν♯ x = ν₁♯ x.1 + ν₂♯ x.2 := rfl

theorem ν_mkL (p : V × V) :
    ν♯ (LocalizedModule.mk p.1 1, LocalizedModule.mk p.2 1) = LocalizedModule.mk p 1 := by
  rw [ν_apply, ν₁, ν₂, semiLift_mk_one, semiLift_mk_one, κ₁_apply, κ₂_apply, ← mk_one_add]
  simp

theorem ν₁_smulL (z : Loc DV) (x : DV.ML) : ν₁♯ (z • x) = ψL♯ z • ν₁♯ x := by
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective DV.mTheta.primeCompl z
  rw [ν₁, semiLift_mk'_smul, ψL_mk']

theorem ν₂_smulL (z : Loc DV) (x : DV.ML) : ν₂♯ (z • x) = ψL♯ z • ν₂♯ x := by
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective DV.mTheta.primeCompl z
  rw [ν₂, semiLift_mk'_smul, ψL_mk']

theorem ν_smulL (z : Loc DV) (x : DV.ML × DV.ML) : ν♯ (z • x) = ψL♯ z • ν♯ x := by
  rw [ν_apply, ν_apply, Prod.smul_fst, Prod.smul_snd, ν₁_smulL, ν₂_smulL, smul_add]

theorem ν_smul (f : DV.FreeAlg) (x : DV.ML × DV.ML) : ν♯ (f • x) = ψ♯ f • ν♯ x := by
  rw [← IsScalarTower.algebraMap_smul (Loc DV) f x, ν_smulL, ψL_algebraMap]

theorem ψL_τHat : ψL♯ (τHat DV σV) = ψτ DP σP c d := by
  rw [τHat, ψL_algebraMap, ψ_X_inr]

theorem ψL_dHatV : ψL♯ (dHatV DV σV d) = dHat DP σP d := by
  rw [dHatV, ψL_algebraMap, ψ_X_inl]; rfl

include hprod hc in
theorem isUnit_dHatV : IsUnit (dHatV DV σV d) :=
  isUnit_algebraMap_X DV (δ_ne_zero DV σV c d α β hprod hc)

theorem map_ringInverse {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {x : A} (hx : IsUnit x) :
    φ (Ring.inverse x) = Ring.inverse (φ x) := by
  obtain ⟨u, rfl⟩ := hx
  rw [Ring.inverse_unit]
  have : φ (u : A) = (Units.map (φ : A →* B) u : B) := rfl
  rw [this, Ring.inverse_unit, Units.coe_map_inv]
  rfl

theorem uHat_ν₂ (x : DV.ML) : uHat DP σP • ν₂♯ x = algebraMap 𝒪 (Loc DP) c • ν₁♯ x := by
  induction x using LocalizedModule.induction_on with
  | h v s =>
    rw [ν₁_mk, ν₂_mk, ← mul_smul, mul_comm, mul_smul, κ₂_apply, uHat_smul_mk, hopP_inr, comp_apply,
      κ₁_apply, ← mul_smul (algebraMap 𝒪 (Loc DP) c), mul_comm, mul_smul]
    congr 1
    rw [IsScalarTower.algebraMap_smul, ← mk_one_smul]
    simp

theorem uHat_ν₁ (x : DV.ML) :
    uHat DP σP • ν₁♯ x = ψτ DP σP c d • ν₁♯ x - Ring.inverse (dHat DP σP d) • ν₂♯ x := by
  have hu := isUnit_uHat DV DP σV σP c d α β hα hprod hc
  have hd := isUnit_dHat DV DP σV σP c d α β hθ hprod hc
  induction x using LocalizedModule.induction_on with
  | h v s =>
    rw [ν₁_mk, ν₂_mk, ← mul_smul, mul_comm, mul_smul, κ₁_apply, uHat_smul_mk, hopP_inr, comp_apply,
      ← mul_smul (ψτ DP σP c d), mul_comm, mul_smul, ← mul_smul (Ring.inverse (dHat DP σP d)),
      mul_comm, mul_smul, ← smul_sub]
    congr 1
    rw [ψτ_smul_mk DV DP σV σP c d Dinv hopP_inl hopP_inr hDinv hDinv' hu hd]

    have hinv : Ring.inverse (dHat DP σP d) • (LocalizedModule.mk (0, v) 1 : DP.ML) =
        LocalizedModule.mk (0, Dinv v) 1 := by
      apply smul_injective_of_isUnit DP hd
      rw [← mul_smul, Ring.mul_inverse_cancel _ hd, one_smul, dHat_smul_mk, hopP_inl]
      simp only [diag_apply, map_zero]
      rw [show DV.op (σV (Sum.inl d)) (Dinv v) = v from
        congrArg (fun f : Module.End 𝒪 V => f v) hDinv]
    rw [κ₂_apply, hinv, sub_eq_add_neg, ← mk_one_neg, ← mk_one_add]
    simp

theorem ν_uL (x : DV.ML × DV.ML) : ν♯ (uL DV σV c d x) = uHat DP σP • ν♯ x := by
  have hd := isUnit_dHat DV DP σV σP c d α β hθ hprod hc
  have hdV := isUnit_dHatV DV σV c d α β hprod hc
  rw [uL_apply, ν_apply, ν_apply, smul_add, map_add, map_neg, uHat_ν₁, uHat_ν₂, ν₁_smulL, ν₁_smulL,
    ν₂_smulL, ψL_τHat, map_ringInverse _ hdV, ψL_dHatV,
    IsScalarTower.algebraMap_apply 𝒪 DV.FreeAlg (Loc DV), ψL_algebraMap, AlgHom.commutes]
  abel
end API
end Localised

section Hensel
variable [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Module.Finite 𝒪 V]
  (hk : Function.Surjective (algebraMap 𝒪 k))
  (α β : k) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
  (hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k c) (hc : algebraMap 𝒪 k c ≠ 0)

def φV : Loc DV →ₐ[𝒪] Module.End 𝒪 DV.ML := Algebra.lsmul 𝒪 𝒪 DV.ML

theorem φV_apply (z : Loc DV) (x : DV.ML) : φV DV z x = z • x := rfl

theorem finite_end (M : Type) [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M] :
    Module.Finite 𝒪 (Module.End 𝒪 M) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' 𝒪 M
  have hinj : Function.Injective (LinearMap.lcomp 𝒪 M π : Module.End 𝒪 M →ₗ[𝒪] ((Fin n → 𝒪) →ₗ[𝒪] M)) := by
    intro f g hfg
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    exact congrArg (fun h : (Fin n → 𝒪) →ₗ[𝒪] M => h y) hfg
  exact Module.Finite.of_injective _ hinj

include hk in

theorem isLocalHom_algebraMap_loc : IsLocalHom (algebraMap 𝒪 (Loc DV)) := by
  constructor
  intro a ha
  by_contra hna
  have hmem : a ∈ maximalIdeal 𝒪 := hna
  have h0 : algebraMap 𝒪 k a = 0 := by
    have : a ∈ RingHom.ker (algebraMap 𝒪 k) := by
      rw [IsLocalRing.ker_eq_maximalIdeal (algebraMap 𝒪 k) hk]; exact hmem
    exact this
  have := (isUnit_iff_Θ_ne_zero DV _).mp ha
  rw [Θ_algebraMap_base] at this
  exact this h0

theorem hensel_quadratic {R : Type} [CommRing R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]
    (t e a₀ : R) (h1 : a₀ * a₀ - t * a₀ + e ∈ maximalIdeal R) (h2 : IsUnit (2 * a₀ - t)) :
    ∃ a : R, a * a - t * a + e = 0 ∧ a - a₀ ∈ maximalIdeal R := by
  set f : Polynomial R := Polynomial.X * Polynomial.X - (Polynomial.C t * Polynomial.X - Polynomial.C e)
    with hf
  have hdeg2 : (Polynomial.X * Polynomial.X : Polynomial R).degree = 2 := by
    rw [(Polynomial.monic_X).degree_mul, Polynomial.degree_X]; rfl
  have hfmonic : f.Monic := by
    apply (Polynomial.monic_X.mul Polynomial.monic_X).sub_of_left
    calc (Polynomial.C t * Polynomial.X - Polynomial.C e).degree
        ≤ 1 := (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_le _)
          (Polynomial.degree_C_le.trans (by norm_num)))
      _ < (Polynomial.X * Polynomial.X : Polynomial R).degree := by rw [hdeg2]; norm_num
  have hfeval : ∀ a, f.eval a = a * a - t * a + e := fun a => by
    simp only [hf, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hfderiv : ∀ a, f.derivative.eval a = 2 * a - t := fun a => by
    simp only [hf, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.derivative_C, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero]
    ring
  have h1' : f.eval a₀ ∈ maximalIdeal R := by rw [hfeval]; exact h1
  have h2' : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval a₀)) := by
    rw [hfderiv]; exact h2.map _
  obtain ⟨a, hroot, hcong⟩ := HenselianRing.is_henselian (R := R) (I := maximalIdeal R) f hfmonic a₀ h1' h2'
  refine ⟨a, ?_, hcong⟩
  have := hroot
  rwa [Polynomial.IsRoot, hfeval] at this

include hk hT hprod hc in

theorem exists_root [Nontrivial DV.ML] (hne : α ≠ β) :
    ∃ A : Loc DV, Θ DV A = α ∧ ∀ x : DV.ML,
      (A * A - τHat DV σV * A + algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d)) • x = 0 := by
  classical

  set I : Ideal (Loc DV) := RingHom.ker (φV DV) with hI
  have hI_ne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : Loc DV) ∈ I := h ▸ Submodule.mem_top
    have h2 : φV DV 1 = 0 := h1
    rw [map_one] at h2
    obtain ⟨x, hx⟩ := exists_ne (0 : DV.ML)
    exact hx (by simpa using congrArg (fun f : Module.End 𝒪 DV.ML => f x) h2)
  haveI : Nontrivial (Loc DV ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
  haveI : IsLocalRing (Loc DV ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI hmkloc : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  haveI : Module.Finite 𝒪 DV.ML := (CohCarrier.HeckeData.finite_ML_and_free_ML hk DV).1
  haveI : Module.Finite 𝒪 (Module.End 𝒪 DV.ML) := finite_end (𝒪 := 𝒪) DV.ML
  haveI : IsNoetherian 𝒪 (Module.End 𝒪 DV.ML) := isNoetherian_of_isNoetherianRing_of_finite 𝒪 _
  let L0 : (Loc DV ⧸ I) →+* Module.End 𝒪 DV.ML :=
    RingHom.kerLift (φV DV : Loc DV →+* Module.End 𝒪 DV.ML)
  have hL0 : Function.Injective L0 := RingHom.kerLift_injective _
  let L : (Loc DV ⧸ I) →ₗ[𝒪] Module.End 𝒪 DV.ML :=
    { toFun := L0
      map_add' := map_add L0
      map_smul' := fun a x => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, RingHom.id_apply]
        show φV DV (algebraMap 𝒪 (Loc DV) a * x) = a • φV DV x
        rw [map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] }
  haveI : Module.Finite 𝒪 (Loc DV ⧸ I) := Module.Finite.of_injective L hL0

  haveI : IsLocalHom (algebraMap 𝒪 (Loc DV ⧸ I)) := by
    haveI := isLocalHom_algebraMap_loc DV hk
    rw [show algebraMap 𝒪 (Loc DV ⧸ I) = (Ideal.Quotient.mk I).comp (algebraMap 𝒪 (Loc DV)) from
      RingHom.ext fun a => (Ideal.Quotient.mk_algebraMap 𝒪 I a).symm]
    exact RingHom.isLocalHom_comp _ _

  haveI hcpl := IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪) (T := Loc DV ⧸ I)

  obtain ⟨a, ha⟩ := hk α
  set a₀ : Loc DV := algebraMap 𝒪 (Loc DV) a
  have hΘa₀ : Θ DV a₀ = α := by rw [Θ_algebraMap_base, ha]
  have hdV := isUnit_dHatV DV σV c d α β hprod hc
  have hδ0 := δ_ne_zero DV σV c d α β hprod hc
  set tt : Loc DV := τHat DV σV
  set ee : Loc DV := algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d)

  have h1' : Ideal.Quotient.mk I (a₀ * a₀ - tt * a₀ + ee) ∈ maximalIdeal (Loc DV ⧸ I) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (a₀ * a₀ - tt * a₀ + ee) := isUnit_of_map_unit (Ideal.Quotient.mk I) _ hu
    revert hu'
    rw [imp_false, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, mem_maximalIdeal_iff_Θ_eq_zero,
      map_add, map_sub, map_mul, map_mul, hΘa₀]
    simp only [tt, ee, τHat, Θ_X, hT, map_mul, Θ_inverse DV hdV, Θ_algebraMap_base]
    rw [dHatV, Θ_X, ← hprod]
    field_simp
    ring
  have h1 : Ideal.Quotient.mk I a₀ * Ideal.Quotient.mk I a₀ - Ideal.Quotient.mk I tt * Ideal.Quotient.mk I a₀
      + Ideal.Quotient.mk I ee ∈ maximalIdeal (Loc DV ⧸ I) := by
    have := h1'
    rwa [map_add, map_sub, map_mul, map_mul] at this

  have h2' : IsUnit (Ideal.Quotient.mk I (2 * a₀ - tt)) := by
    apply IsUnit.map
    rw [isUnit_iff_Θ_ne_zero, map_sub, map_mul, map_ofNat, hΘa₀]
    simp only [tt, τHat, Θ_X, hT]
    intro h
    apply hne
    have : α - β = 0 := by rw [← h]; ring
    exact sub_eq_zero.mp this
  have h2 : IsUnit (2 * Ideal.Quotient.mk I a₀ - Ideal.Quotient.mk I tt) := by
    have := h2'
    rwa [map_sub, map_mul, map_ofNat] at this

  obtain ⟨Ab, hroot, hcong⟩ := hensel_quadratic (R := Loc DV ⧸ I) (Ideal.Quotient.mk I tt)
    (Ideal.Quotient.mk I ee) (Ideal.Quotient.mk I a₀) h1 h2
  obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective Ab
  refine ⟨A, ?_, ?_⟩
  ·
    have hnu : ¬ IsUnit (Ideal.Quotient.mk I (A - a₀)) := by
      rw [map_sub]; exact (IsLocalRing.mem_maximalIdeal _).mp hcong
    have hnu' : ¬ IsUnit (A - a₀) := fun h => hnu (h.map _)
    have h0 : Θ DV (A - a₀) = 0 := by
      rwa [isUnit_iff_Θ_ne_zero, not_not] at hnu'
    rw [map_sub, hΘa₀, sub_eq_zero] at h0
    exact h0
  ·
    intro x
    have hr : Ideal.Quotient.mk I (A * A - τHat DV σV * A + algebraMap 𝒪 (Loc DV) c *
        Ring.inverse (dHatV DV σV d)) = 0 := by
      simpa [tt, ee] using hroot
    have hmem : A * A - τHat DV σV * A + algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d) ∈ I :=
      Ideal.Quotient.eq_zero_iff_mem.mp hr
    exact congrArg (fun f : Module.End 𝒪 DV.ML => f x) (RingHom.mem_ker.mp hmem)
end Hensel

section Split
variable (α β : k)
  (hθ : ∀ g : G, DP.θbar (σP (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))
  (hα : DP.θbar (σP (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
  (hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k c) (hc : algebraMap 𝒪 k c ≠ 0)
  (hne : α ≠ β)
  (Dinv : Module.End 𝒪 V)
  (hopP_inl : ∀ g : G, DP.op (σP (Sum.inl g)) = diag (DV.op (σV (Sum.inl g))))
  (hopP_inr : DP.op (σP (Sum.inr ())) = comp (DV.op (σV (Sum.inr ()))) Dinv c)
  (hDinv : DV.op (σV (Sum.inl d)) * Dinv = 1) (hDinv' : Dinv * DV.op (σV (Sum.inl d)) = 1)
  (A : Loc DV) (hΘA : Θ DV A = α)
  (hAroot : ∀ x : DV.ML,
    (A * A - τHat DV σV * A + algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d)) • x = 0)

def Bt : Loc DV := τHat DV σV - A

def KA : Submodule (Loc DV) (DV.ML × DV.ML) :=
  LinearMap.ker (uL DV σV c d - A • LinearMap.id)

theorem mem_KA_iff (x : DV.ML × DV.ML) : x ∈ KA DV σV c d A ↔ uL DV σV c d x = A • x := by
  rw [KA, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

include hprod hc in
theorem isUnit_c' : IsUnit (algebraMap 𝒪 (Loc DV) c) := by
  rw [isUnit_iff_Θ_ne_zero, Θ_algebraMap_base]; exact hc

include hT hΘA hne in

theorem isUnit_A_sub_Bt : IsUnit (A - Bt DV σV A) := by
  rw [isUnit_iff_Θ_ne_zero, Bt, map_sub, map_sub, hΘA, τHat, Θ_X, hT]
  intro h; apply hne
  have : α - β = 0 := by rw [← h]; ring
  exact sub_eq_zero.mp this

include hprod hc hΘA in
theorem isUnit_A : IsUnit A := by
  rw [isUnit_iff_Θ_ne_zero, hΘA]; exact α_ne_zero DV σV c d α β hprod hc

include hAroot in

theorem A_Bt_smul (x : DV.ML) :
    (A * Bt DV σV A) • x = (algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d)) • x := by
  rw [show A * Bt DV σV A = -(A * A - τHat DV σV * A + algebraMap 𝒪 (Loc DV) c *
      Ring.inverse (dHatV DV σV d)) + algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d) by
    rw [Bt]; ring, add_smul, neg_smul, hAroot x, neg_zero, zero_add]

include hAroot in
theorem A_Bt_smul₂ (x : DV.ML × DV.ML) :
    (A * Bt DV σV A) • x = (algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d)) • x :=
  Prod.ext (A_Bt_smul DV σV c d A hAroot x.1) (A_Bt_smul DV σV c d A hAroot x.2)

theorem uL_uL (x : DV.ML × DV.ML) :
    uL DV σV c d (uL DV σV c d x) = τHat DV σV • uL DV σV c d x -
      (algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d)) • x := by
  obtain ⟨x₁, x₂⟩ := x
  simp only [uL_apply]
  ext
  · simp only [Prod.smul_mk, Prod.mk_sub_mk]
    rw [smul_neg, ← mul_smul, sub_eq_add_neg]
  · simp only [Prod.smul_mk, Prod.mk_sub_mk]
    rw [smul_add, ← mul_smul, ← mul_smul, smul_neg, ← mul_smul, mul_comm _ (τHat DV σV),
      mul_comm (Ring.inverse (dHatV DV σV d)) (algebraMap 𝒪 (Loc DV) c), neg_add, sub_eq_add_neg]

include hAroot in

theorem uL_sub_Bt_mem (x : DV.ML × DV.ML) : uL DV σV c d x - Bt DV σV A • x ∈ KA DV σV c d A := by
  rw [mem_KA_iff, map_sub, LinearMap.map_smul, uL_uL, smul_sub, ← mul_smul A (Bt DV σV A),
    A_Bt_smul₂ DV σV c d A hAroot,
    show A • uL DV σV c d x = τHat DV σV • uL DV σV c d x - Bt DV σV A • uL DV σV c d x by
      rw [Bt, sub_smul]; abel]
  abel

def E : Loc DV := Ring.inverse (A - Bt DV σV A)

def πA : (DV.ML × DV.ML) →ₗ[Loc DV] KA DV σV c d A where
  toFun x := ⟨E DV σV A • (uL DV σV c d x - Bt DV σV A • x),
    (KA DV σV c d A).smul_mem _ (uL_sub_Bt_mem DV σV c d A hAroot x)⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    rw [smul_add (Bt DV σV A) x y, ← smul_add (E DV σV A)]; congr 1; abel
  map_smul' r x := by
    apply Subtype.ext
    simp only [LinearMap.map_smul, RingHom.id_apply, Submodule.coe_smul]
    rw [← mul_smul, mul_comm (Bt DV σV A) r, mul_smul, ← smul_sub, ← mul_smul, mul_comm, mul_smul]

theorem coe_πA (x : DV.ML × DV.ML) :
    (πA DV σV c d A hAroot x : DV.ML × DV.ML) = E DV σV A • (uL DV σV c d x - Bt DV σV A • x) := rfl

include hT hne hΘA in
theorem E_mul : E DV σV A * (A - Bt DV σV A) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_A_sub_Bt DV σV α β hT hne A hΘA)

include hT hΘA hne in

theorem πA_of_mem {x : DV.ML × DV.ML} (hx : x ∈ KA DV σV c d A) :
    (πA DV σV c d A hAroot x : DV.ML × DV.ML) = x := by
  have h : uL DV σV c d x - Bt DV σV A • x = (A - Bt DV σV A) • x := by
    rw [(mem_KA_iff DV σV c d A x).mp hx, sub_smul]
  rw [coe_πA, h, ← mul_smul, E_mul DV σV α β hT hne A hΘA, one_smul]

include hT hΘA hne in

theorem decomp (x : DV.ML × DV.ML) :
    ∃ y : DV.ML × DV.ML, uL DV σV c d y = Bt DV σV A • y ∧ x = πA DV σV c d A hAroot x + y := by
  refine ⟨E DV σV A • (A • x - uL DV σV c d x), ?_, ?_⟩
  ·
    have key : uL DV σV c d (A • x - uL DV σV c d x) = Bt DV σV A • (A • x - uL DV σV c d x) := by
      have hAu : A • uL DV σV c d x = τHat DV σV • uL DV σV c d x - Bt DV σV A • uL DV σV c d x := by
        rw [Bt, sub_smul]; abel
      have hBA : Bt DV σV A • A • x = (algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d)) • x := by
        rw [← mul_smul, mul_comm, A_Bt_smul₂ DV σV c d A hAroot]
      rw [map_sub, LinearMap.map_smul, uL_uL, hAu, smul_sub (Bt DV σV A), hBA]
      abel
    rw [LinearMap.map_smul, key, ← mul_smul, ← mul_smul, mul_comm]
  · rw [coe_πA, ← smul_add, sub_add_sub_cancel', show A • x - Bt DV σV A • x = (A - Bt DV σV A) • x by
      rw [sub_smul], ← mul_smul, E_mul DV σV α β hT hne A hΘA, one_smul]

section NuKills
local notation "ν♯" => ν DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv'
local notation "ψL♯" => ψL DV DP σV σP c d α β hθ hα hT hprod hc

include hΘA hne in
theorem ν_eq_zero_of_uL_eq {y : DV.ML × DV.ML} (hy : uL DV σV c d y = Bt DV σV A • y) : ν♯ y = 0 := by
  have hunit : IsUnit (uHat DP σP - ψL♯ (Bt DV σV A)) := by
    rw [isUnit_iff_Θ_ne_zero, map_sub, Θ_ψL, uHat, Θ_X, hα, Bt, map_sub, hΘA, τHat, Θ_X, hT]
    intro h; apply hne
    have : α - β = 0 := by rw [← h]; ring
    exact sub_eq_zero.mp this
  apply smul_injective_of_isUnit DP hunit
  rw [smul_zero, sub_smul, ← ν_uL, hy, ν_smulL, sub_self]

include hΘA hne in

theorem ν_πA (x : DV.ML × DV.ML) : ν♯ (πA DV σV c d A hAroot x : DV.ML × DV.ML) = ν♯ x := by
  obtain ⟨y, hy, hxy⟩ := decomp DV σV c d α β hT hne A hΘA hAroot x
  conv_rhs => rw [hxy]
  rw [map_add, ν_eq_zero_of_uL_eq DV DP σV σP c d α β hθ hα hT hprod hc hne Dinv hopP_inl hopP_inr hDinv hDinv'
    A hΘA hy, add_zero]
end NuKills

def cinv : Loc DV := Ring.inverse (algebraMap 𝒪 (Loc DV) c)

include hprod hc in
theorem c_mul_cinv : algebraMap 𝒪 (Loc DV) c * cinv DV c = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_c' DV σV c d α β hprod hc)

def toKA : DV.ML →ₗ[Loc DV] KA DV σV c d A where
  toFun m := ⟨(m, -((cinv DV c * Bt DV σV A) • m)), by
    rw [mem_KA_iff]
    have hcc := c_mul_cinv DV σV c d α β hprod hc
    ext
    · rw [uL_apply, Prod.smul_mk]
      show τHat DV σV • m + algebraMap 𝒪 (Loc DV) c • -((cinv DV c * Bt DV σV A) • m) = A • m
      rw [smul_neg, ← mul_smul, ← mul_assoc, hcc, one_mul, Bt, sub_smul]
      abel
    · rw [uL_apply, Prod.smul_mk]
      show -(Ring.inverse (dHatV DV σV d) • m) = A • -((cinv DV c * Bt DV σV A) • m)
      have hcc' : cinv DV c * algebraMap 𝒪 (Loc DV) c = 1 := by rw [mul_comm]; exact hcc
      rw [smul_neg, ← mul_smul, neg_inj, mul_left_comm, mul_smul,
        A_Bt_smul DV σV c d A hAroot m, ← mul_smul, ← mul_assoc, hcc', one_mul]⟩
  map_add' m m' := by
    apply Subtype.ext
    show (m + m', -((cinv DV c * Bt DV σV A) • (m + m'))) =
      (m, -((cinv DV c * Bt DV σV A) • m)) + (m', -((cinv DV c * Bt DV σV A) • m'))
    rw [Prod.mk_add_mk, smul_add, neg_add]
  map_smul' r m := by
    apply Subtype.ext
    show (r • m, -((cinv DV c * Bt DV σV A) • r • m)) = r • (m, -((cinv DV c * Bt DV σV A) • m))
    rw [Prod.smul_mk, smul_neg, ← mul_smul, ← mul_smul, mul_comm r]

theorem coe_toKA (m : DV.ML) :
    (toKA DV σV c d α β hprod hc A hAroot m : DV.ML × DV.ML) = (m, -((cinv DV c * Bt DV σV A) • m)) := rfl

def fromKA : KA DV σV c d A →ₗ[Loc DV] DV.ML := (LinearMap.fst _ _ _).comp (KA DV σV c d A).subtype

theorem fromKA_apply (y : KA DV σV c d A) : fromKA DV σV c d A y = (y : DV.ML × DV.ML).1 := rfl

theorem fromKA_toKA (m : DV.ML) : fromKA DV σV c d A (toKA DV σV c d α β hprod hc A hAroot m) = m := rfl

theorem toKA_fromKA (y : KA DV σV c d A) :
    toKA DV σV c d α β hprod hc A hAroot (fromKA DV σV c d A y) = y := by
  apply Subtype.ext
  rw [coe_toKA, fromKA_apply]
  obtain ⟨⟨x₁, x₂⟩, hx⟩ := y
  have h1 := congrArg Prod.fst ((mem_KA_iff DV σV c d A _).mp hx)
  simp only [uL_apply, Prod.smul_mk] at h1

  have h2 : algebraMap 𝒪 (Loc DV) c • x₂ = -(Bt DV σV A • x₁) := by
    rw [Bt, sub_smul, ← h1]; abel
  have hcc : cinv DV c * algebraMap 𝒪 (Loc DV) c = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_c' DV σV c d α β hprod hc)
  show (x₁, -((cinv DV c * Bt DV σV A) • x₁)) = (x₁, x₂)
  rw [mul_smul, ← smul_neg, ← h2, ← mul_smul, hcc, one_smul]

def KAEquiv : KA DV σV c d A ≃ₗ[Loc DV] DV.ML :=
  { fromKA DV σV c d A with
    invFun := toKA DV σV c d α β hprod hc A hAroot
    left_inv := toKA_fromKA DV σV c d α β hprod hc A hAroot
    right_inv := fromKA_toKA DV σV c d α β hprod hc A hAroot }

def ψ' : DP.FreeAlg →ₐ[𝒪] Loc DV :=
  MvPolynomial.aeval fun γ => Sum.elim
    (fun g => algebraMap DV.FreeAlg (Loc DV) (MvPolynomial.X (σV (Sum.inl g)))) (fun _ => A) (σP.symm γ)

theorem ψ'_X_inl (g : G) :
    ψ' DV DP σV σP A (MvPolynomial.X (σP (Sum.inl g))) =
      algebraMap DV.FreeAlg (Loc DV) (MvPolynomial.X (σV (Sum.inl g))) := by
  rw [ψ', MvPolynomial.aeval_X, Equiv.symm_apply_apply]; rfl

theorem ψ'_X_inr : ψ' DV DP σV σP A (MvPolynomial.X (σP (Sum.inr ()))) = A := by
  rw [ψ', MvPolynomial.aeval_X, Equiv.symm_apply_apply]; rfl

include hθ hα hΘA in

theorem Θ_ψ' (f : DP.FreeAlg) : Θ DV (ψ' DV DP σV σP A f) = DP.thetaTilde f := by
  suffices h : (ΘA DV).comp (ψ' DV DP σV σP A) = DP.thetaTilde from
    congrArg (fun φ : DP.FreeAlg →ₐ[𝒪] k => φ f) h
  apply MvPolynomial.algHom_ext
  intro γ
  obtain ⟨x, rfl⟩ := σP.surjective γ
  show Θ DV (ψ' DV DP σV σP A (MvPolynomial.X (σP x))) = MvPolynomial.aeval DP.θbar (MvPolynomial.X (σP x))
  rw [MvPolynomial.aeval_X]
  rcases x with g | u
  · rw [ψ'_X_inl, Θ_X, hθ]
  · obtain rfl : u = () := rfl
    rw [ψ'_X_inr, hΘA, hα]

include hθ hα hΘA in
theorem isUnit_ψ' (s : DP.mTheta.primeCompl) : IsUnit (ψ' DV DP σV σP A (s : DP.FreeAlg)) := by
  rw [isUnit_iff_Θ_ne_zero, Θ_ψ' DV DP σV σP α hθ hα A hΘA]
  exact thetaTilde_ne_zero_of_mem DP s

def mkL : (V × V) →ₗ[𝒪] DV.ML × DV.ML := (DV.toMLₒ ∘ₗ LinearMap.fst 𝒪 V V).prod (DV.toMLₒ ∘ₗ LinearMap.snd 𝒪 V V)

theorem mkL_apply (p : V × V) : mkL DV p = (LocalizedModule.mk p.1 1, LocalizedModule.mk p.2 1) := rfl

theorem mk_T (v : V) :
    (LocalizedModule.mk (DV.op (σV (Sum.inr ())) v) 1 : DV.ML) = τHat DV σV • LocalizedModule.mk v 1 := by
  rw [τHat, algebraMap_smul_ML, X_smul_mk]

include hDinv hprod hc in
theorem mk_Dinv (v : V) :
    (LocalizedModule.mk (Dinv v) 1 : DV.ML) = Ring.inverse (dHatV DV σV d) • LocalizedModule.mk v 1 := by
  have hdV := isUnit_dHatV DV σV c d α β hprod hc
  apply smul_injective_of_isUnit DV hdV
  rw [← mul_smul, Ring.mul_inverse_cancel _ hdV, one_smul, dHatV, algebraMap_smul_ML, X_smul_mk,
    show DV.op (σV (Sum.inl d)) (Dinv v) = v from congrArg (fun f : Module.End 𝒪 V => f v) hDinv]

include hDinv hprod hc in

theorem mkL_comp (p : V × V) :
    mkL DV (comp (DV.op (σV (Sum.inr ()))) Dinv c p) = uL DV σV c d (mkL DV p) := by
  rw [mkL_apply, mkL_apply, comp_apply, uL_apply]
  ext
  · show (LocalizedModule.mk (DV.op (σV (Sum.inr ())) p.1 + c • p.2) 1 : DV.ML) = _
    rw [show (LocalizedModule.mk (DV.op (σV (Sum.inr ())) p.1 + c • p.2) 1 : DV.ML) =
      LocalizedModule.mk (DV.op (σV (Sum.inr ())) p.1) 1 + LocalizedModule.mk (c • p.2) 1 from
        (LocalizedModule.mkLinearMap DV.mTheta.primeCompl V).map_add _ _, mk_T,
      IsScalarTower.algebraMap_smul]
    congr 1
    rw [← IsScalarTower.algebraMap_smul DV.FreeAlg c (LocalizedModule.mk p.2 1), LocalizedModule.smul'_mk,
      algebraMap_smul]
  · show (LocalizedModule.mk (-(Dinv p.1)) 1 : DV.ML) = _
    rw [show (LocalizedModule.mk (-(Dinv p.1)) 1 : DV.ML) = -LocalizedModule.mk (Dinv p.1) 1 from
      (LocalizedModule.mkLinearMap DV.mTheta.primeCompl V).map_neg _, mk_Dinv DV σV c d α β hprod hc Dinv hDinv]

theorem mkL_diag (f : DV.FreeAlg) (T : Module.End 𝒪 V) (hT : ∀ v, (LocalizedModule.mk (T v) 1 : DV.ML) =
    algebraMap DV.FreeAlg (Loc DV) f • LocalizedModule.mk v 1) (p : V × V) :
    mkL DV (diag T p) = algebraMap DV.FreeAlg (Loc DV) f • mkL DV p := by
  rw [mkL_apply, mkL_apply, diag_apply, Prod.smul_mk, hT, hT]

def lam₀ : (V × V) →ₗ[𝒪] KA DV σV c d A := (πA DV σV c d A hAroot).restrictScalars 𝒪 ∘ₗ mkL DV

theorem lam₀_apply (p : V × V) : lam₀ DV σV c d A hAroot p = πA DV σV c d A hAroot (mkL DV p) := rfl

include hopP_inl hopP_inr hDinv hprod hc in

theorem lam₀_smul (f : DP.FreeAlg) (p : V × V) :
    lam₀ DV σV c d A hAroot (f • p) = ψ' DV DP σV σP A f • lam₀ DV σV c d A hAroot p := by
  induction f using MvPolynomial.induction_on generalizing p with
  | C a =>
    rw [show (MvPolynomial.C a : DP.FreeAlg) = algebraMap 𝒪 DP.FreeAlg a from rfl, algebraMap_smul,
      AlgHom.commutes, IsScalarTower.algebraMap_smul, map_smul]
  | add p' q hp hq => rw [add_smul, map_add, hp, hq, map_add, add_smul]
  | mul_X p' γ hp =>
    rw [mul_smul, hp, map_mul, mul_smul]
    congr 1
    obtain ⟨x, rfl⟩ := σP.surjective γ
    rcases x with g | u
    · rw [ψ'_X_inl, X_smul_raw, hopP_inl, lam₀_apply, lam₀_apply,
        mkL_diag DV (MvPolynomial.X (σV (Sum.inl g))) _ (fun v => by rw [algebraMap_smul_ML, X_smul_mk]),
        LinearMap.map_smul]
    · obtain rfl : u = () := rfl
      rw [ψ'_X_inr, X_smul_raw, hopP_inr, lam₀_apply, lam₀_apply, mkL_comp DV σV c d α β hprod hc Dinv hDinv]
      apply Subtype.ext
      rw [Submodule.coe_smul, ← (mem_KA_iff DV σV c d A _).mp (πA DV σV c d A hAroot (mkL DV p)).2, coe_πA,
        coe_πA, LinearMap.map_smul, map_sub, LinearMap.map_smul, uL_uL]

section Lam
variable [IsNoetherianRing 𝒪]

local notation "ν♯" => ν DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv'
local notation "ψL♯" => ψL DV DP σV σP c d α β hθ hα hT hprod hc
local notation "hS'♯" => isUnit_ψ' DV DP σV σP α hθ hα A hΘA

def lam : DP.ML →ₗ[𝒪] KA DV σV c d A :=
  semiLift (A := 𝒪) (R := DP.FreeAlg) (M := V × V) (B := Loc DV) (N := KA DV σV c d A)
    DP.mTheta.primeCompl (ψ' DV DP σV σP A) (lam₀ DV σV c d A hAroot)
    (lam₀_smul DV DP σV σP c d α β hprod hc Dinv hopP_inl hopP_inr hDinv A hAroot) hS'♯

local notation "lam♯" => lam DV DP σV σP c d α β hθ hα hprod hc Dinv hopP_inl hopP_inr hDinv A hΘA hAroot

def mu : KA DV σV c d A →ₗ[𝒪] DP.ML := ν♯ ∘ₗ (KA DV σV c d A).subtype.restrictScalars 𝒪

local notation "μ♯" => mu DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv' A

theorem mu_apply (y : KA DV σV c d A) : μ♯ y = ν♯ (y : DV.ML × DV.ML) := rfl

theorem lam_mk_one (p : V × V) : lam♯ (LocalizedModule.mk p 1) = lam₀ DV σV c d A hAroot p := semiLift_mk_one _ _ _ _ _ p

theorem lam_smul (f : DP.FreeAlg) (z : DP.ML) : lam♯ (f • z) = ψ' DV DP σV σP A f • lam♯ z := semiLift_smul _ _ _ _ _ f z

include hne in

theorem mu_lam_X (γ : DP.Gen) (z : DP.ML) :
    μ♯ (lam♯ ((MvPolynomial.X γ : DP.FreeAlg) • z)) = (MvPolynomial.X γ : DP.FreeAlg) • μ♯ (lam♯ z) := by
  rw [lam_smul, mu_apply, mu_apply, Submodule.coe_smul, ν_smulL]
  obtain ⟨x, rfl⟩ := σP.surjective γ
  rcases x with g | u
  · rw [ψ'_X_inl, ψL_algebraMap, ψ_X_inl, algebraMap_smul_ML]
  · obtain rfl : u = () := rfl
    rw [ψ'_X_inr, ← ν_smulL, ← (mem_KA_iff DV σV c d A _).mp (lam♯ z).2, ν_uL, uHat, algebraMap_smul_ML]

include hne in

theorem mu_lam_smul (f : DP.FreeAlg) (z : DP.ML) : μ♯ (lam♯ (f • z)) = f • μ♯ (lam♯ z) := by
  induction f using MvPolynomial.induction_on generalizing z with
  | C a =>
    rw [show (MvPolynomial.C a : DP.FreeAlg) = algebraMap 𝒪 DP.FreeAlg a from rfl, algebraMap_smul,
      algebraMap_smul, map_smul, map_smul]
  | add p q hp hq => rw [add_smul, map_add, map_add, hp, hq, add_smul]
  | mul_X p γ hp => rw [mul_smul, hp, mu_lam_X (hne := hne), mul_smul]

include hne in

theorem mu_lam (z : DP.ML) : μ♯ (lam♯ z) = z := by
  induction z using LocalizedModule.induction_on with
  | h p s =>
    apply smul_loc_injective s
    have hcancel : (LocalizedModule.mk ((s : DP.FreeAlg) • p) s : DP.ML) = LocalizedModule.mk p 1 := by
      rw [LocalizedModule.mk_eq]; exact ⟨1, by simp [Submonoid.smul_def]⟩
    rw [← mu_lam_smul (hne := hne), LocalizedModule.smul'_mk, hcancel, lam_mk_one, mu_apply,
      lam₀_apply, ν_πA (hne := hne) (hΘA := hΘA), mkL_apply, ν_mkL]

def ψ'L : Loc DP →+* Loc DV :=
  IsLocalization.lift (M := DP.mTheta.primeCompl) (g := (ψ' DV DP σV σP A).toRingHom) hS'♯

local notation "ψ'L♯" => ψ'L DV DP σV σP α hθ hα A hΘA

theorem ψ'L_algebraMap (f : DP.FreeAlg) : ψ'L♯ (algebraMap DP.FreeAlg (Loc DP) f) = ψ' DV DP σV σP A f :=
  IsLocalization.lift_eq _ f

theorem ψ'L_mk' (f : DP.FreeAlg) (s : DP.mTheta.primeCompl) :
    ψ'L♯ (IsLocalization.mk' (Loc DP) f s) = ψ' DV DP σV σP A f * uinv DP.mTheta.primeCompl (ψ' DV DP σV σP A) hS'♯ s := by
  have h1 : ψ'L♯ (IsLocalization.mk' (Loc DP) f s) * ψ' DV DP σV σP A (s : DP.FreeAlg) = ψ' DV DP σV σP A f := by
    rw [← ψ'L_algebraMap DV DP σV σP α hθ hα A hΘA (s : DP.FreeAlg), ← map_mul, IsLocalization.mk'_spec,
      ψ'L_algebraMap]
  calc ψ'L♯ (IsLocalization.mk' (Loc DP) f s)
      = ψ'L♯ (IsLocalization.mk' (Loc DP) f s) * (ψ' DV DP σV σP A (s : DP.FreeAlg) *
          uinv DP.mTheta.primeCompl (ψ' DV DP σV σP A) hS'♯ s) := by rw [mul_uinv, mul_one]
    _ = _ := by rw [← mul_assoc, h1]

theorem lam_smulL (w : Loc DP) (z : DP.ML) : lam♯ (w • z) = ψ'L♯ w • lam♯ z := by
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective DP.mTheta.primeCompl w
  rw [lam, semiLift_mk'_smul, ψ'L_mk']

include hprod hc hne hAroot in

theorem ψ'L_ψτ_smul (m : DV.ML) : ψ'L♯ (ψτ DP σP c d) • m = τHat DV σV • m := by
  have hu := isUnit_uHat DV DP σV σP c d α β hα hprod hc
  have hd := isUnit_dHat DV DP σV σP c d α β hθ hprod hc
  have hA := isUnit_A DV σV c d α β hprod hc A hΘA
  have hbase : ψ'L♯ (algebraMap 𝒪 (Loc DP) c) = algebraMap 𝒪 (Loc DV) c := by
    rw [IsScalarTower.algebraMap_apply 𝒪 DP.FreeAlg (Loc DP), ψ'L_algebraMap, AlgHom.commutes]
  rw [ψτ, map_add, map_mul, map_mul, map_ringInverse _ hu, map_ringInverse _ hd, uHat, dHat,
    ψ'L_algebraMap, ψ'L_algebraMap, ψ'_X_inr, ψ'_X_inl, hbase]

  apply smul_injective_of_isUnit DV hA
  rw [← mul_smul, mul_add,
    show A * (algebraMap 𝒪 (Loc DV) c * (Ring.inverse (algebraMap DV.FreeAlg (Loc DV)
      (MvPolynomial.X (σV (Sum.inl d)))) * Ring.inverse A)) = (A * Ring.inverse A) *
      (algebraMap 𝒪 (Loc DV) c * Ring.inverse (dHatV DV σV d)) by rw [dHatV]; ring,
    Ring.mul_inverse_cancel _ hA, one_mul, add_smul, ← A_Bt_smul DV σV c d A hAroot m, ← add_smul,
    ← mul_add, Bt, add_sub_cancel, mul_smul]

include hprod hc hne hAroot in

theorem twist_smul (f : DV.FreeAlg) (m : DV.ML) : ψ'L♯ (ψ DV DP σV σP c d f) • m = f • m := by
  induction f using MvPolynomial.induction_on generalizing m with
  | C a =>
    rw [show (MvPolynomial.C a : DV.FreeAlg) = algebraMap 𝒪 DV.FreeAlg a from rfl, AlgHom.commutes,
      IsScalarTower.algebraMap_apply 𝒪 DP.FreeAlg (Loc DP), ψ'L_algebraMap, AlgHom.commutes,
      IsScalarTower.algebraMap_smul, algebraMap_smul]
  | add p q hp hq => rw [map_add, map_add, add_smul, hp, hq, add_smul]
  | mul_X p γ hp =>
    rw [map_mul, map_mul, mul_smul, mul_smul]
    obtain ⟨x, rfl⟩ := σV.surjective γ
    rcases x with g | u
    · rw [ψ_X_inl, ψ'L_algebraMap, ψ'_X_inl, algebraMap_smul_ML, hp]
    · obtain rfl : u = () := rfl
      rw [ψ_X_inr, ψ'L_ψτ_smul (β := β) (hprod := hprod) (hc := hc) (hne := hne) (hAroot := hAroot),
        τHat, algebraMap_smul_ML, hp]

include hprod hc hne hAroot in
theorem twist_smul₂ (f : DV.FreeAlg) (x : DV.ML × DV.ML) : ψ'L♯ (ψ DV DP σV σP c d f) • x = f • x :=
  Prod.ext (twist_smul DV DP σV σP c d α β hθ hα hprod hc hne A hΘA hAroot f x.1)
    (twist_smul DV DP σV σP c d α β hθ hα hprod hc hne A hΘA hAroot f x.2)

include hT hne in

theorem lam_surjective : Function.Surjective lam♯ := by
  intro y
  obtain ⟨⟨x₁, x₂⟩, hx⟩ := y
  induction x₁ using LocalizedModule.induction_on with
  | h v₁ s₁ =>
    induction x₂ using LocalizedModule.induction_on with
    | h v₂ s₂ =>

      set s : DV.mTheta.primeCompl := s₁ * s₂ with hs
      set p' : V × V := ((s₂ : DV.FreeAlg) • v₁, (s₁ : DV.FreeAlg) • v₂) with hp'
      have hsx : (s : DV.FreeAlg) • ((LocalizedModule.mk v₁ s₁, LocalizedModule.mk v₂ s₂) : DV.ML × DV.ML) =
          mkL DV p' := by
        rw [Prod.smul_mk, mkL_apply, hp', hs, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk,
          Submonoid.coe_mul, mul_smul, mul_comm, mul_smul]
        simp only [Prod.mk.injEq]
        constructor
        · rw [show ((s₁ : DV.FreeAlg) • (s₂ : DV.FreeAlg) • v₁) = s₁ • ((s₂ : DV.FreeAlg) • v₁) from rfl,
            LocalizedModule.mk_cancel]
        · rw [show ((s₂ : DV.FreeAlg) • (s₁ : DV.FreeAlg) • v₂) = s₂ • ((s₁ : DV.FreeAlg) • v₂) from rfl,
            LocalizedModule.mk_cancel]

      have hy : (s : DV.FreeAlg) • (⟨(LocalizedModule.mk v₁ s₁, LocalizedModule.mk v₂ s₂), hx⟩ : KA DV σV c d A) =
          lam♯ (LocalizedModule.mk p' 1) := by
        rw [lam_mk_one, lam₀_apply]
        apply Subtype.ext
        rw [Submodule.coe_smul_of_tower, ← hsx,
          πA_of_mem DV σV c d α β hT hne A hΘA hAroot ((KA DV σV c d A).smul_of_tower_mem _ hx)]

      let w : Loc DP := Ring.inverse (ψ DV DP σV σP c d (s : DV.FreeAlg))
      have hws : ψ'L♯ w * ψ'L♯ (ψ DV DP σV σP c d (s : DV.FreeAlg)) = 1 := by
        rw [← map_mul, Ring.inverse_mul_cancel _ (isUnit_ψ DV DP σV σP c d α β hθ hα hT hprod hc s), map_one]
      refine ⟨w • LocalizedModule.mk p' 1, ?_⟩
      rw [lam_smulL, ← hy]
      apply Subtype.ext
      rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
        ← twist_smul₂ DV DP σV σP c d α β hθ hα hprod hc hne A hΘA hAroot, ← mul_smul, hws, one_smul]

include hT hne in

theorem lam_mu (y : KA DV σV c d A) : lam♯ (μ♯ y) = y := by
  obtain ⟨z, rfl⟩ := lam_surjective DV DP σV σP c d α β hθ hα hT hprod hc hne Dinv hopP_inl hopP_inr hDinv A hΘA hAroot y
  rw [mu_lam (hne := hne)]

def PEquiv : DP.ML ≃ₗ[𝒪] KA DV σV c d A :=
  { lam♯ with
    invFun := μ♯
    left_inv := mu_lam DV DP σV σP c d α β hθ hα hT hprod hc hne Dinv hopP_inl hopP_inr hDinv hDinv' A hΘA hAroot
    right_inv := lam_mu DV DP σV σP c d α β hθ hα hT hprod hc hne Dinv hopP_inl hopP_inr hDinv hDinv' A hΘA hAroot }
end Lam
end Split
end Setting

section Main
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

theorem main (hk : Function.Surjective (algebraMap 𝒪 k))
    (DV : HeckeData 𝒪 V k) (DP : HeckeData 𝒪 (V × V) k)
    {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σP : G ⊕ Unit ≃ DP.Gen)
    (hθ : ∀ g : G, DP.θbar (σP (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))
    (c : 𝒪) (d : G) (Dinv : Module.End 𝒪 V)
    (hDinv : DV.op (σV (Sum.inl d)) * Dinv = 1) (hDinv' : Dinv * DV.op (σV (Sum.inl d)) = 1)
    (hop_inl : ∀ g : G, DP.op (σP (Sum.inl g)) = (DV.op (σV (Sum.inl g))).prodMap (DV.op (σV (Sum.inl g))))
    (hop_inr : DP.op (σP (Sum.inr ())) =
      (DV.op (σV (Sum.inr ())) ∘ₗ LinearMap.fst 𝒪 V V + c • LinearMap.snd 𝒪 V V).prod
        (-(Dinv ∘ₗ LinearMap.fst 𝒪 V V)))
    (α β : k) (hα : DP.θbar (σP (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
    (hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k c) (hc : algebraMap 𝒪 k c ≠ 0)
    (hne : α ≠ β) :
    ∃ e : DP.ML ≃ₗ[𝒪] DV.ML, ∀ (g : G) (x : DP.ML),
      e ((MvPolynomial.X (σP (Sum.inl g)) : DP.FreeAlg) • x) =
        (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) • e x := by
  have hopP_inl : ∀ g : G, DP.op (σP (Sum.inl g)) = diag (DV.op (σV (Sum.inl g))) := hop_inl
  have hopP_inr : DP.op (σP (Sum.inr ())) = comp (DV.op (σV (Sum.inr ()))) Dinv c := hop_inr
  rcases subsingleton_or_nontrivial DV.ML with hV | hV
  ·
    haveI : Subsingleton DP.ML := by
      refine ⟨fun x y => ?_⟩
      suffices h : ∀ z : DP.ML, z = 0 by rw [h x, h y]
      intro z
      induction z using LocalizedModule.induction_on with
      | h p s =>
        apply smul_loc_injective s
        have hcancel : (LocalizedModule.mk ((s : DP.FreeAlg) • p) s : DP.ML) = LocalizedModule.mk p 1 := by
          rw [LocalizedModule.mk_eq]; exact ⟨1, by simp [Submonoid.smul_def]⟩
        rw [smul_zero, LocalizedModule.smul'_mk, hcancel,
          ← ν_mkL DV DP σV σP c d α β hθ hα hT hprod hc Dinv hopP_inl hopP_inr hDinv hDinv' p,
          Subsingleton.elim (LocalizedModule.mk p.1 1, LocalizedModule.mk p.2 1) 0, map_zero]
    exact ⟨LinearEquiv.ofSubsingleton DP.ML DV.ML, fun g x => Subsingleton.elim _ _⟩
  ·
    obtain ⟨A, hΘA, hAroot⟩ := exists_root DV σV c d hk α β hT hprod hc hne
    refine ⟨(PEquiv DV DP σV σP c d α β hθ hα hT hprod hc hne Dinv hopP_inl hopP_inr hDinv hDinv' A hΘA hAroot).trans
      ((KAEquiv DV σV c d α β hprod hc A hAroot).restrictScalars 𝒪), fun g x => ?_⟩
    show fromKA DV σV c d A (lam DV DP σV σP c d α β hθ hα hprod hc Dinv hopP_inl hopP_inr hDinv A hΘA hAroot
        ((MvPolynomial.X (σP (Sum.inl g)) : DP.FreeAlg) • x)) =
      (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) •
        fromKA DV σV c d A (lam DV DP σV σP c d α β hθ hα hprod hc Dinv hopP_inl hopP_inr hDinv A hΘA hAroot x)
    rw [lam_smul, ψ'_X_inl, fromKA_apply, fromKA_apply, Submodule.coe_smul, Prod.smul_fst, algebraMap_smul_ML]
end Main
end TWCompanion
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion.TWCompanion"

open CohCarrier in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

    (DV : HeckeData 𝒪 V k) (DP : HeckeData 𝒪 (V × V) k)

    {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σP : G ⊕ Unit ≃ DP.Gen)
    (hθ : ∀ g : G, DP.θbar (σP (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))

    (c : 𝒪) (d : G) (Dinv : Module.End 𝒪 V)
    (hDinv : DV.op (σV (Sum.inl d)) * Dinv = 1) (hDinv' : Dinv * DV.op (σV (Sum.inl d)) = 1)

    (hop_inl : ∀ g : G,
      DP.op (σP (Sum.inl g)) = (DV.op (σV (Sum.inl g))).prodMap (DV.op (σV (Sum.inl g))))
    (hop_inr : DP.op (σP (Sum.inr ())) =
      (DV.op (σV (Sum.inr ())) ∘ₗ LinearMap.fst 𝒪 V V + c • LinearMap.snd 𝒪 V V).prod
        (-(Dinv ∘ₗ LinearMap.fst 𝒪 V V)))

    (α β : k) (hα : DP.θbar (σP (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
    (hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k c) (hc : algebraMap 𝒪 k c ≠ 0)
    (hne : α ≠ β) :
    ∃ e : DP.ML ≃ₗ[𝒪] DV.ML, ∀ (g : G) (x : DP.ML),
      e ((MvPolynomial.X (σP (Sum.inl g)) : DP.FreeAlg) • x) =
        (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) • e x :=
  TWCompanion.main hk DV DP σV σP hθ c d Dinv hDinv hDinv' hop_inl hop_inr α β hα hT hprod hc hne

end
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion.TWCompanion"

end S_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion
end P2MW
export P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion (solution)
