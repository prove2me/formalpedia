-- Prove2me | solution 1 for GaloisRep.exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/85c76a7b-1261-5661-a4bc-dde56406094f

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure
import Theorems.Thm_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq
import Theorems.Thm_GaloisRep_ratLocalizedAt_isUnit_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct

namespace P2mWeilRestriction

abbrev Γℚ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

abbrev Qb : Type := AlgebraicClosure ℚ

abbrev Rp (p : ℕ) : Type := GaloisRep.ratLocalizedAt p

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

scoped instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

theorem finite_algHom_of_moduleFinite {R A L : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Field L] [Algebra R L] : Finite (A →ₐ[R] L) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A

  let T : (x : A) → Set L := fun x => {v | (minpoly R x).map (algebraMap R L) ≠ 0 →
    v ∈ ((minpoly R x).map (algebraMap R L)).roots}
  have hT : ∀ x, (T x).Finite := by
    intro x
    by_cases h0 : (minpoly R x).map (algebraMap R L) = 0
    ·
      exact absurd h0 ((minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _).ne_zero
    · refine (((minpoly R x).map (algebraMap R L)).roots.toFinset.finite_toSet).subset ?_
      intro v hv
      simpa using hv h0
  let Φ : (A →ₐ[R] L) → (s → L) := fun f x => f x
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    apply AlgHom.toLinearMap_injective
    apply LinearMap.ext
    intro a
    have ha : a ∈ Submodule.span R (s : Set A) := by rw [hs]; exact Submodule.mem_top
    refine LinearMap.eqOn_span (fun x hx => ?_) ha
    exact congrFun hfg ⟨x, hx⟩
  have hΦmem : ∀ f, Φ f ∈ Set.pi Set.univ (fun x : s => T x) := by
    intro f x _ h0
    rw [Polynomial.mem_roots h0, Polynomial.IsRoot.def, Polynomial.eval_map,
      ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  haveI : Finite (Set.pi Set.univ (fun x : s => T x)) :=
    (Set.Finite.pi fun x : s => hT x).to_subtype
  exact Finite.of_injective (fun f => (⟨Φ f, hΦmem f⟩ : Set.pi Set.univ (fun x : s => T x)))
    fun f g h => hΦ (congrArg Subtype.val h)

section points

variable {p : ℕ} {G : Type} [CommRing G] [HopfAlgebra (Rp p) G]
  {M : Type} [AddCommGroup M] [DistribMulAction Γℚ M]
  (e : WithConv (G →ₐ[Rp p] Qb) ≃ M)

def E (h : G) (m : M) : Qb := (e.symm m).ofConv h

theorem E_def (h : G) (m : M) : E e h m = (e.symm m).ofConv h := rfl

theorem E_add_left (h h' : G) (m : M) : E e (h + h') m = E e h m + E e h' m := map_add _ _ _

theorem E_mul_left (h h' : G) (m : M) : E e (h * h') m = E e h m * E e h' m := map_mul _ _ _

theorem E_smul_left (r : Rp p) (h : G) (m : M) :
    E e (r • h) m = algebraMap (Rp p) Qb r * E e h m := by
  rw [E_def, E_def, ← Algebra.smul_def]
  exact (e.symm m).ofConv.toLinearMap.map_smul r h

theorem E_algebraMap (r : Rp p) (m : M) : E e (algebraMap (Rp p) G r) m = algebraMap (Rp p) Qb r :=
  (e.symm m).ofConv.commutes r

theorem E_one_left (m : M) : E e 1 m = 1 := map_one _

def evalAlgHom {X : Type} (π : X → M) : G →ₐ[Rp p] (X → Qb) where
  toFun h := fun x => E e h (π x)
  map_one' := funext fun x => E_one_left e (π x)
  map_mul' h h' := funext fun x => E_mul_left e h h' (π x)
  map_zero' := funext fun x => map_zero _
  map_add' h h' := funext fun x => E_add_left e h h' (π x)
  commutes' r := funext fun x => E_algebraMap e r (π x)

theorem evalAlgHom_apply {X : Type} (π : X → M) (h : G) (x : X) :
    evalAlgHom e π h x = E e h (π x) := rfl

variable (he_add : ∀ f g, e (f * g) = e f + e g)

include he_add

theorem symm_add (m m' : M) : e.symm (m + m') = e.symm m * e.symm m' :=
  e.injective (by rw [he_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

theorem symm_zero : e.symm 0 = 1 := by
  have h : e 1 + e 1 = e 1 := by rw [← he_add, one_mul]
  have h1 : e 1 = 0 := by simpa using h
  rw [← h1, Equiv.symm_apply_apply]

theorem E_zero_right (h : G) : E e h 0 = algebraMap (Rp p) Qb (Coalgebra.counit h) := by
  rw [E_def, symm_zero e he_add]; rfl

theorem E_add_right {h : G} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr (Rp p) h ι𝓡) (m m' : M) :
    E e h (m + m') = ∑ i ∈ 𝓡.index, E e (𝓡.left i) m * E e (𝓡.right i) m' := by
  rw [E_def, symm_add e he_add]
  have h1 := 𝓡.convMul_apply (WithConv.toConv (e.symm m).ofConv.toLinearMap)
    (WithConv.toConv (e.symm m').ofConv.toLinearMap)
  rw [← AlgHom.toLinearMap_convMul] at h1
  exact h1

def antipodeAlgHom : G →ₐ[Rp p] G :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode (Rp p)) HopfAlgebra.antipode_one
    fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm]

theorem antipodeAlgHom_apply (h : G) : antipodeAlgHom (p := p) (G := G) h = HopfAlgebra.antipode (Rp p) h :=
  rfl

theorem E_neg_right (h : G) (m : M) : E e h (-m) = E e (HopfAlgebra.antipode (Rp p) h) m := by
  classical

  set f : WithConv (G →ₐ[Rp p] Qb) := e.symm m with hf
  set g : WithConv (G →ₐ[Rp p] Qb) := WithConv.toConv (f.ofConv.comp antipodeAlgHom) with hg
  have hgf : g * f = 1 := by
    apply WithConv.ext
    apply AlgHom.toLinearMap_injective
    have h2 := congrArg WithConv.ofConv (AlgHom.toLinearMap_convMul g f)
    change (g * f).ofConv.toLinearMap = _ at h2
    rw [h2]
    apply LinearMap.ext
    intro a
    let 𝓡 := Coalgebra.Repr.arbitrary (Rp p) a
    rw [𝓡.convMul_apply]
    change ∑ i ∈ 𝓡.index, f.ofConv (HopfAlgebra.antipode (Rp p) (𝓡.left i)) * f.ofConv (𝓡.right i) =
      (1 : WithConv (G →ₐ[Rp p] Qb)).ofConv a
    rw [AlgHom.convOne_apply]
    simp_rw [← map_mul]
    rw [← map_sum, HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit, AlgHom.commutes]
  have hnf : e.symm (-m) * f = 1 := by rw [hf, ← symm_add e he_add, neg_add_cancel, symm_zero e he_add]
  have hfn : f * e.symm (-m) = 1 := by rw [hf, ← symm_add e he_add, add_neg_cancel, symm_zero e he_add]
  have hEq : e.symm (-m) = g := (left_inv_eq_right_inv hgf hfn).symm
  rw [E_def, hEq]
  rfl

omit he_add

variable (he_act : ∀ (σ : Γℚ) (f g : WithConv (G →ₐ[Rp p] Qb)),
  (∀ x : G, g x = σ (f x)) → e g = σ • (e f))

include he_act

theorem E_smul_right (σ : Γℚ) (h : G) (m : M) : E e h (σ • m) = σ (E e h m) := by
  let g : WithConv (G →ₐ[Rp p] Qb) :=
    WithConv.toConv (((σ : Qb ≃ₐ[ℚ] Qb) : Qb →ₐ[ℚ] Qb).restrictScalars (Rp p) |>.comp
      (e.symm m).ofConv)
  have hg : e g = σ • m := by
    have := he_act σ (e.symm m) g (fun x => rfl)
    rwa [Equiv.apply_symm_apply] at this
  rw [E_def, ← hg, Equiv.symm_apply_apply]
  rfl

omit he_act

theorem E_injective {m m' : M} (h : ∀ x : G, E e x m = E e x m') : m = m' := by
  apply e.symm.injective
  apply WithConv.ext
  exact AlgHom.ext h

end points

section galoisSet

variable {S : Type} [MulAction Γℚ S] (K : IntermediateField ℚ Qb) [Normal ℚ K]

noncomputable def lift (γ : K ≃ₐ[ℚ] K) : Γℚ :=
  Function.surjInv (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)) γ

theorem restrictNormalHom_lift (γ : K ≃ₐ[ℚ] K) : AlgEquiv.restrictNormalHom K (lift K γ) = γ :=
  Function.surjInv_eq (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)) γ

theorem coe_restrictNormalHom (σ : Γℚ) (x : K) :
    ((AlgEquiv.restrictNormalHom (K₁ := Qb) K σ x : K) : Qb) = σ (x : Qb) :=
  AlgEquiv.restrictNormal_commutes σ K x

theorem coe_lift_apply (γ : K ≃ₐ[ℚ] K) (x : K) : ((γ x : K) : Qb) = lift K γ (x : Qb) := by
  have h := coe_restrictNormalHom K (lift K γ) x
  rwa [restrictNormalHom_lift] at h

variable (hS : ∀ σ : Γℚ, (∀ x ∈ K, σ x = x) → ∀ s : S, σ • s = s)
include hS

theorem smul_eq_of_restrict_eq {τ τ' : Γℚ}
    (h : AlgEquiv.restrictNormalHom K τ = AlgEquiv.restrictNormalHom K τ') (s : S) :
    τ • s = τ' • s := by
  have h1 : ∀ x ∈ K, (τ'⁻¹ * τ) x = x := by
    intro x hx
    have h2 := congrArg (fun γ : K ≃ₐ[ℚ] K => ((γ ⟨x, hx⟩ : K) : Qb)) h
    simp only [coe_restrictNormalHom] at h2
    change τ'⁻¹ (τ x) = x
    rw [h2]
    exact τ'.symm_apply_apply x
  have h3 := hS _ h1 s
  rw [mul_smul] at h3
  calc τ • s = τ' • τ'⁻¹ • τ • s := by rw [smul_inv_smul]
    _ = τ' • s := by rw [h3]

theorem lift_restrict_smul (σ : Γℚ) (s : S) :
    lift K (AlgEquiv.restrictNormalHom K σ) • s = σ • s :=
  smul_eq_of_restrict_eq K hS (by rw [restrictNormalHom_lift]) s

theorem lift_one_smul (s : S) : lift K 1 • s = s := by
  rw [← map_one (AlgEquiv.restrictNormalHom (K₁ := Qb) K), lift_restrict_smul K hS, one_smul]

theorem lift_mul_smul (γ δ : K ≃ₐ[ℚ] K) (s : S) : lift K (γ * δ) • s = lift K γ • lift K δ • s := by
  rw [← mul_smul]
  refine smul_eq_of_restrict_eq K hS ?_ s
  rw [map_mul, restrictNormalHom_lift, restrictNormalHom_lift, restrictNormalHom_lift]

theorem inv_smul_lift_smul (σ : Γℚ) (γ : K ≃ₐ[ℚ] K) (s : S) :
    σ⁻¹ • lift K γ • s = lift K ((AlgEquiv.restrictNormalHom K σ)⁻¹ * γ) • s := by
  rw [← mul_smul]
  refine smul_eq_of_restrict_eq K hS ?_ s
  rw [map_mul, map_inv, restrictNormalHom_lift, restrictNormalHom_lift]

end galoisSet

def TwFun (S N : Type) : Type := S → N

scoped instance (S N : Type) [AddCommGroup N] : AddCommGroup (TwFun S N) :=
  inferInstanceAs (AddCommGroup (S → N))

scoped instance (S N : Type) [Finite S] [Finite N] : Finite (TwFun S N) :=
  inferInstanceAs (Finite (S → N))

def TwFun.val {S N : Type} (φ : TwFun S N) : S → N := φ

def TwFun.mk {S N : Type} (φ : S → N) : TwFun S N := φ

@[scoped simp] theorem TwFun.val_mk {S N : Type} (φ : S → N) : (TwFun.mk φ).val = φ := rfl
p2m_reactivate "P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.P2mWeilRestriction.TwFun"
@[scoped simp] theorem TwFun.mk_val {S N : Type} (φ : TwFun S N) : TwFun.mk φ.val = φ := rfl

p2m_reactivate "P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.P2mWeilRestriction.TwFun"
theorem TwFun.ext {S N : Type} {φ ψ : TwFun S N} (h : ∀ s, φ.val s = ψ.val s) : φ = ψ :=
  funext h

theorem TwFun.val_add {S N : Type} [AddCommGroup N] (φ ψ : TwFun S N) (s : S) :
    (φ + ψ).val s = φ.val s + ψ.val s := rfl

theorem TwFun.val_zero {S N : Type} [AddCommGroup N] (s : S) : (0 : TwFun S N).val s = 0 := rfl

theorem TwFun.val_neg {S N : Type} [AddCommGroup N] (φ : TwFun S N) (s : S) :
    (-φ).val s = -(φ.val s) := rfl

scoped instance twFunDistribMulAction (S N : Type) [MulAction Γℚ S] [AddCommGroup N]
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

section construction

variable {p : ℕ} {G : Type} [CommRing G] [HopfAlgebra (Rp p) G]
  {M : Type} [AddCommGroup M] [DistribMulAction Γℚ M]
  (e : WithConv (G →ₐ[Rp p] Qb) ≃ M)
  {S : Type} [MulAction Γℚ S] (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K] [Normal ℚ K]

def FF (c : K) (s : S) (h : G) : TwFun S M → Qb :=
  fun φ => ∑ γ : K ≃ₐ[ℚ] K, ((γ c : K) : Qb) * E e h (φ.val (lift K γ • s))

theorem FF_apply (c : K) (s : S) (h : G) (φ : TwFun S M) :
    FF e K c s h φ = ∑ γ : K ≃ₐ[ℚ] K, ((γ c : K) : Qb) * E e h (φ.val (lift K γ • s)) := rfl

theorem FF_eq_sum_evalAlgHom (c : K) (s : S) (h : G) :
    FF e K c s h = ∑ γ : K ≃ₐ[ℚ] K, algebraMap Qb (TwFun S M → Qb) ((γ c : K) : Qb) *
      evalAlgHom e (fun φ : TwFun S M => φ.val (lift K γ • s)) h := by
  funext φ
  rw [FF_apply, Finset.sum_apply]
  rfl

theorem FF_add_left (c c' : K) (s : S) (h : G) : FF e K (c + c') s h = FF e K c s h + FF e K c' s h := by
  funext φ
  simp only [FF_apply, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  push_cast
  ring

theorem FF_zero_left (s : S) (h : G) : FF e K 0 s h = 0 := by
  funext φ
  simp [FF_apply]

theorem FF_zsmul_left (n : ℤ) (c : K) (s : S) (h : G) : FF e K (n • c) s h = n • FF e K c s h := by
  funext φ
  simp only [FF_apply, Pi.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_mul, map_intCast]
  push_cast
  ring

theorem FF_add_right (c : K) (s : S) (h h' : G) : FF e K c s (h + h') = FF e K c s h + FF e K c s h' := by
  rw [FF_eq_sum_evalAlgHom, FF_eq_sum_evalAlgHom, FF_eq_sum_evalAlgHom, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_add, mul_add]

theorem FF_zero_right (c : K) (s : S) : FF e K c s 0 = 0 := by
  rw [FF_eq_sum_evalAlgHom]
  simp

theorem FF_smul_right (c : K) (s : S) (r : Rp p) (h : G) :
    FF e K c s (r • h) = algebraMap (Rp p) (TwFun S M → Qb) r * FF e K c s h := by
  funext φ
  change FF e K c s (r • h) φ = algebraMap (Rp p) Qb r * FF e K c s h φ
  rw [FF_apply, FF_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [E_smul_left]
  ring

theorem isIntegral_of_int {y : Qb} (hy : IsIntegral ℤ y) : IsIntegral (Rp p) y := by
  obtain ⟨P, hm, hP⟩ := hy
  refine ⟨P.map (Int.castRingHom (Rp p)), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map,
    RingHom.ext_int ((algebraMap (Rp p) Qb).comp (Int.castRingHom (Rp p))) (algebraMap ℤ Qb)]
  exact hP

theorem isIntegral_FF [Module.Finite (Rp p) G] {c : K} (hc : IsIntegral ℤ c) (s : S) (h : G) :
    IsIntegral (Rp p) (FF e K c s h) := by
  rw [FF_eq_sum_evalAlgHom]
  refine IsIntegral.sum _ fun γ _ => IsIntegral.mul ?_ ?_
  · refine IsIntegral.algebraMap ?_
    have h1 : IsIntegral ℤ ((γ c : K) : Qb) :=
      map_isIntegral_int (algebraMap K Qb) (map_isIntegral_int (γ : K ≃ₐ[ℚ] K) hc)
    exact isIntegral_of_int h1
  · haveI : Algebra.IsIntegral (Rp p) G := Algebra.IsIntegral.of_finite (Rp p) G
    exact (Algebra.IsIntegral.isIntegral h).map _

variable (hS : ∀ σ : Γℚ, (∀ x ∈ K, σ x = x) → ∀ s : S, σ • s = s)

variable (he_act : ∀ (σ : Γℚ) (f g : WithConv (G →ₐ[Rp p] Qb)),
  (∀ x : G, g x = σ (f x)) → e g = σ • (e f))

include hS he_act in

theorem FF_smul (c : K) (s : S) (h : G) (σ : Γℚ) (φ : TwFun S M) :
    FF e K c s h (σ • φ) = σ (FF e K c s h φ) := by
  set σb : K ≃ₐ[ℚ] K := AlgEquiv.restrictNormalHom (K₁ := Qb) K σ with hσb
  rw [FF_apply, FF_apply, map_sum]
  have h1 : ∀ γ : K ≃ₐ[ℚ] K, ((γ c : K) : Qb) * E e h ((σ • φ).val (lift K γ • s)) =
      ((γ c : K) : Qb) * σ (E e h (φ.val (lift K (σb⁻¹ * γ) • s))) := by
    intro γ
    rw [TwFun.val_smul, E_smul_right e he_act, inv_smul_lift_smul K hS]
  rw [Finset.sum_congr rfl fun γ _ => h1 γ]
  refine Fintype.sum_equiv (Equiv.mulLeft σb⁻¹) _ _ fun γ => ?_
  rw [Equiv.coe_mulLeft, map_mul]
  congr 1
  have h2 : γ = σb * (σb⁻¹ * γ) := (mul_inv_cancel_left σb γ).symm
  conv_lhs => rw [h2]
  rw [AlgEquiv.mul_apply, hσb, coe_restrictNormalHom]

variable (he_add : ∀ f g, e (f * g) = e f + e g)

include he_add in

theorem FF_neg (c : K) (s : S) (h : G) (φ : TwFun S M) :
    FF e K c s h (-φ) = FF e K c s (HopfAlgebra.antipode (Rp p) h) φ := by
  rw [FF_apply, FF_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [TwFun.val_neg, E_neg_right e he_add]

include hS in

theorem E_val_eq_sum_FF {n : ℕ} (a b : Fin n → K)
    (h1 : ∀ γ : K ≃ₐ[ℚ] K, ∑ j, γ (a j) * γ (b j) = 1)
    (h0 : ∀ γ δ : K ≃ₐ[ℚ] K, γ ≠ δ → ∑ j, γ (a j) * δ (b j) = 0)
    (s : S) (h : G) (θ : TwFun S M) :
    E e h (θ.val s) = ∑ j, ((b j : K) : Qb) * FF e K (a j) s h θ := by
  classical
  have horth : ∀ γ : K ≃ₐ[ℚ] K, ∑ j, ((γ (a j) : K) : Qb) * ((b j : K) : Qb) =
      if γ = 1 then 1 else 0 := by
    intro γ
    have hK : ∑ j, γ (a j) * (1 : K ≃ₐ[ℚ] K) (b j) = if γ = 1 then 1 else 0 := by
      split_ifs with hγ
      · rw [hγ]; exact h1 1
      · exact h0 γ 1 hγ
    have := congrArg (fun x : K => (x : Qb)) hK
    simpa [apply_ite] using this
  simp_rw [FF_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ γ : K ≃ₐ[ℚ] K, ∑ j, ((b j : K) : Qb) * (((γ (a j) : K) : Qb) * E e h (θ.val (lift K γ • s))) =
      (if γ = 1 then 1 else 0) * E e h (θ.val (lift K γ • s)) := by
    intro γ
    rw [← horth γ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl fun γ _ => h2 γ]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [lift_one_smul K hS]

include he_add in

theorem FF_add {n : ℕ} (a b : Fin n → K)
    (h1 : ∀ γ : K ≃ₐ[ℚ] K, ∑ j, γ (a j) * γ (b j) = 1)
    (h0 : ∀ γ δ : K ≃ₐ[ℚ] K, γ ≠ δ → ∑ j, γ (a j) * δ (b j) = 0)
    (d : ℤ) (u : Rp p) (hu : algebraMap (Rp p) Qb u * (d : Qb) = 1)
    (c : K) (s : S) {h : G} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr (Rp p) h ι𝓡) (φ ψ : TwFun S M) :
    FF e K c s h (φ + ψ) = ∑ j, ∑ i ∈ 𝓡.index,
      FF e K (c * a j) s (𝓡.left i) φ *
        (algebraMap (Rp p) (TwFun S M → Qb) u * FF e K ((d : K) * b j) s (𝓡.right i)) ψ := by
  classical
  have horth : ∀ γ δ : K ≃ₐ[ℚ] K, ∑ j, ((γ (a j) : K) : Qb) * ((δ (b j) : K) : Qb) =
      if γ = δ then 1 else 0 := by
    intro γ δ
    have hK : ∑ j, γ (a j) * δ (b j) = if γ = δ then 1 else 0 := by
      split_ifs with hγ
      · rw [hγ]; exact h1 δ
      · exact h0 γ δ hγ
    have := congrArg (fun x : K => (x : Qb)) hK
    simpa [apply_ite] using this

  set A : (K ≃ₐ[ℚ] K) → Qb := fun γ => ((γ c : K) : Qb) with hA
  set P : Fin n → (K ≃ₐ[ℚ] K) → Qb := fun j γ => ((γ (a j) : K) : Qb) with hP
  set Q : Fin n → (K ≃ₐ[ℚ] K) → Qb := fun j γ => ((γ (b j) : K) : Qb) with hQ
  set X : 𝓡.ι → (K ≃ₐ[ℚ] K) → Qb := fun i γ => E e (𝓡.left i) (φ.val (lift K γ • s)) with hX
  set Y : 𝓡.ι → (K ≃ₐ[ℚ] K) → Qb := fun i γ => E e (𝓡.right i) (ψ.val (lift K γ • s)) with hY
  set u' : Qb := algebraMap (Rp p) Qb u with hu'

  have hL : FF e K c s h (φ + ψ) = ∑ γ, ∑ i ∈ 𝓡.index, A γ * (X i γ * Y i γ) := by
    rw [FF_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [TwFun.val_add, E_add_right e he_add 𝓡, Finset.mul_sum]

  have hF1 : ∀ j i, FF e K (c * a j) s (𝓡.left i) φ = ∑ γ, A γ * P j γ * X i γ := by
    intro j i
    rw [FF_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_mul]
    push_cast
    ring
  have hF2 : ∀ j i, (algebraMap (Rp p) (TwFun S M → Qb) u * FF e K ((d : K) * b j) s (𝓡.right i)) ψ =
      u' * ∑ δ, (d : Qb) * Q j δ * Y i δ := by
    intro j i
    change algebraMap (Rp p) Qb u * FF e K ((d : K) * b j) s (𝓡.right i) ψ = _
    rw [FF_apply]
    congr 1
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [map_mul, map_intCast]
    push_cast
    ring
  rw [hL]
  simp_rw [hF1, hF2]

  have h3 : ∀ j i, (∑ γ, A γ * P j γ * X i γ) * (u' * ∑ δ, (d : Qb) * Q j δ * Y i δ) =
      ∑ γ, ∑ δ, A γ * X i γ * Y i δ * (u' * (d : Qb)) * (P j γ * Q j δ) := by
    intro j i
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    ring
  simp_rw [h3]

  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_comm]
  have h4 : ∀ δ, ∑ j, A γ * X i γ * Y i δ * (u' * (d : Qb)) * (P j γ * Q j δ) =
      A γ * X i γ * Y i δ * (if γ = δ then 1 else 0) := by
    intro δ
    rw [← Finset.mul_sum, horth γ δ, hu', hu, mul_one]
  simp_rw [h4]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

end construction
p2m_reactivate "P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.P2mWeilRestriction.TwFun"

section subalgebras

variable {p : ℕ} {X : Type} [AddCommGroup X] [DistribMulAction Γℚ X]

def eqvSubalgebra : Subalgebra (Rp p) (X → Qb) where
  carrier := {F | ∀ (σ : Γℚ) (x : X), F (σ • x) = σ (F x)}
  mul_mem' {F F'} hF hF' := fun σ x => by rw [Pi.mul_apply, Pi.mul_apply, hF, hF', map_mul]
  one_mem' := fun σ x => by rw [Pi.one_apply, Pi.one_apply, map_one]
  add_mem' {F F'} hF hF' := fun σ x => by rw [Pi.add_apply, Pi.add_apply, hF, hF', map_add]
  zero_mem' := fun σ x => by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  algebraMap_mem' r := fun σ x => by
    change algebraMap (Rp p) Qb r = σ (algebraMap (Rp p) Qb r)
    rw [IsScalarTower.algebraMap_apply (Rp p) ℚ Qb, AlgEquiv.commutes]

theorem mem_eqvSubalgebra {F : X → Qb} :
    F ∈ (eqvSubalgebra : Subalgebra (Rp p) (X → Qb)) ↔ ∀ (σ : Γℚ) (x : X), F (σ • x) = σ (F x) :=
  Iff.rfl

def comulSubalgebra (B : Subalgebra (Rp p) (X → Qb)) : Subalgebra (Rp p) (X → Qb) where
  carrier := {F | ∃ (ι : Type) (_ : Fintype ι) (F₁ F₂ : ι → X → Qb),
    (∀ i, F₁ i ∈ B) ∧ (∀ i, F₂ i ∈ B) ∧ ∀ x y : X, F (x + y) = ∑ i, F₁ i x * F₂ i y}
  mul_mem' := by
    rintro F F' ⟨ι, _, F₁, F₂, h₁, h₂, hF⟩ ⟨ι', _, F₁', F₂', h₁', h₂', hF'⟩
    refine ⟨ι × ι', inferInstance, fun k => F₁ k.1 * F₁' k.2, fun k => F₂ k.1 * F₂' k.2,
      fun k => B.mul_mem (h₁ _) (h₁' _), fun k => B.mul_mem (h₂ _) (h₂' _), fun x y => ?_⟩
    rw [Pi.mul_apply, hF, hF', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.mul_apply]
    ring
  one_mem' := ⟨Unit, inferInstance, fun _ => 1, fun _ => 1, fun _ => B.one_mem, fun _ => B.one_mem,
    fun x y => by simp⟩
  add_mem' := by
    rintro F F' ⟨ι, _, F₁, F₂, h₁, h₂, hF⟩ ⟨ι', _, F₁', F₂', h₁', h₂', hF'⟩
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim F₁ F₁', Sum.elim F₂ F₂',
      fun k => by cases k with | inl i => exact h₁ i | inr i => exact h₁' i,
      fun k => by cases k with | inl i => exact h₂ i | inr i => exact h₂' i, fun x y => ?_⟩
    rw [Pi.add_apply, hF, hF', Fintype.sum_sum_type]
    simp
  zero_mem' := ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun i => i.elim, fun i => i.elim,
    fun x y => by simp⟩
  algebraMap_mem' r := ⟨Unit, inferInstance, fun _ => algebraMap (Rp p) (X → Qb) r, fun _ => 1,
    fun _ => B.algebraMap_mem r, fun _ => B.one_mem, fun x y => by simp⟩

theorem mem_comulSubalgebra {B : Subalgebra (Rp p) (X → Qb)} {F : X → Qb} :
    F ∈ comulSubalgebra B ↔ ∃ (ι : Type) (_ : Fintype ι) (F₁ F₂ : ι → X → Qb),
      (∀ i, F₁ i ∈ B) ∧ (∀ i, F₂ i ∈ B) ∧ ∀ x y : X, F (x + y) = ∑ i, F₁ i x * F₂ i y :=
  Iff.rfl

def negAlgHom : (X → Qb) →ₐ[Rp p] (X → Qb) where
  toFun F := fun x => F (-x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem negAlgHom_apply (F : X → Qb) (x : X) : negAlgHom (p := p) F x = F (-x) := rfl

end subalgebras
p2m_reactivate "P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.P2mWeilRestriction.TwFun"

end P2mWeilRestriction
p2m_reactivate "P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.P2mWeilRestriction.TwFun P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.P2mWeilRestriction"

open P2mWeilRestriction in
theorem solution
    (p : ℕ) (hp : p.Prime)
    (G : Type) [CommRing G] [HopfAlgebra (GaloisRep.ratLocalizedAt p) G]
    [Module.Finite (GaloisRep.ratLocalizedAt p) G] [Module.Flat (GaloisRep.ratLocalizedAt p) G]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    {S : Type} [Finite S] [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) S]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : haveI : NumberField K := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ K›
      ¬ (p : ℤ) ∣ NumberField.discr K)
    (hS : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ K, σ x = x) →
      ∀ s : S, σ • s = s) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ (S → M),
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → ∀ s : S, e' g s = σ • (e' f (σ⁻¹ • s)) := by
  classical
  haveI hNF : NumberField K := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ K›

  haveI : Finite (G →ₐ[Rp p] Qb) := finite_algHom_of_moduleFinite
  haveI : Finite (WithConv (G →ₐ[Rp p] Qb)) := Finite.of_equiv _ (WithConv.equiv _).symm
  haveI : Finite M := Finite.of_equiv _ e

  obtain ⟨n, a, b, ha, hb, h1, h0⟩ :=
    NumberField.exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq K
  set d : ℤ := NumberField.discr K with hd
  have hdmem : (d : ℚ) ∈ GaloisRep.ratLocalizedAt p := by
    change (d : ℚ).den.Coprime p
    rw [Rat.den_intCast]
    exact Nat.coprime_one_left p
  set dR : Rp p := ⟨(d : ℚ), hdmem⟩ with hdR
  have hdunit : IsUnit dR := by
    rw [GaloisRep.ratLocalizedAt.isUnit_iff hp dR]
    change ¬ p ∣ (d : ℚ).num.natAbs
    rw [Rat.num_intCast]
    exact fun h => hK (Int.natCast_dvd.mpr h)
  obtain ⟨uu, huu⟩ := hdunit
  set u : Rp p := ((uu⁻¹ : (Rp p)ˣ) : Rp p) with hudef
  have hudR : u * dR = 1 := by rw [hudef, ← huu, Units.inv_mul]
  have halg : algebraMap (Rp p) Qb dR = (d : Qb) := by
    rw [IsScalarTower.algebraMap_apply (Rp p) ℚ Qb]
    change algebraMap ℚ Qb (d : ℚ) = (d : Qb)
    rw [map_intCast]
  have hu : algebraMap (Rp p) Qb u * (d : Qb) = 1 := by
    rw [← halg, ← map_mul, hudR, map_one]

  obtain ⟨gs, hgs⟩ := Module.Finite.fg_top (R := Rp p) (M := G)
  set w := NumberField.integralBasis K with hw
  have hwint : ∀ i, IsIntegral ℤ (w i) := fun i => by
    rw [hw, NumberField.integralBasis_apply]; exact NumberField.RingOfIntegers.isIntegral_coe _

  let gen : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) × S × (gs : Set G) →
      TwFun S M → Qb := fun t => FF e K (w t.1) t.2.1 (t.2.2 : G)
  set B : Subalgebra (Rp p) (TwFun S M → Qb) := Algebra.adjoin (Rp p) (Set.range gen) with hB
  have hgenB : ∀ t, gen t ∈ B := fun t => Algebra.subset_adjoin ⟨t, rfl⟩

  have hmemw : ∀ i s (h : G), FF e K (w i) s h ∈ B := by
    intro i s h
    have hh : h ∈ Submodule.span (Rp p) (gs : Set G) := by rw [hgs]; exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hh
    · intro g hg
      exact hgenB (i, s, ⟨g, hg⟩)
    · rw [FF_zero_right]; exact B.zero_mem
    · intro x y _ _ hx hy
      rw [FF_add_right]; exact B.add_mem hx hy
    · intro r x _ hx
      rw [FF_smul_right]; exact B.mul_mem (B.algebraMap_mem r) hx
  have hmem : ∀ c : K, IsIntegral ℤ c → ∀ s (h : G), FF e K c s h ∈ B := by
    intro c hc s h
    have hc' : (c : K) ∈ Submodule.span ℤ (Set.range w) := by
      rw [hw, NumberField.mem_span_integralBasis K]
      exact ⟨⟨c, hc⟩, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hc'
    · rintro _ ⟨i, rfl⟩
      exact hmemw i s h
    · rw [FF_zero_left]; exact B.zero_mem
    · intro x y _ _ hx hy
      rw [FF_add_left]; exact B.add_mem hx hy
    · intro m x _ hx
      rw [FF_zsmul_left]; exact zsmul_mem hx m

  have hfin : (Subalgebra.toSubmodule B).FG := by
    refine fg_adjoin_of_finite (Set.finite_range gen) ?_
    rintro _ ⟨t, rfl⟩
    exact isIntegral_FF e K (hwint t.1) _ _

  have hequiv : ∀ F ∈ B, ∀ (σ : Γℚ) (x : TwFun S M), F (σ • x) = σ (F x) := by
    have hle : B ≤ eqvSubalgebra := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨t, rfl⟩
      exact fun σ x => FF_smul e K hS he_act _ _ _ σ x
    exact fun F hF => hle hF

  have hcomul' : B ≤ comulSubalgebra B := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨i, s, g⟩, rfl⟩
    let 𝓡 := Coalgebra.Repr.arbitrary (Rp p) (g : G)
    refine ⟨Fin n × (𝓡.index : Set 𝓡.ι), inferInstance,
      fun k => FF e K (w i * a k.1) s (𝓡.left k.2),
      fun k => algebraMap (Rp p) (TwFun S M → Qb) u * FF e K ((d : K) * b k.1) s (𝓡.right k.2),
      fun k => hmem _ ((hwint i).mul (ha k.1)) _ _,
      fun k => B.mul_mem (B.algebraMap_mem u) (hmem _ (hb k.1) _ _), fun x y => ?_⟩
    change FF e K (w i) s (g : G) (x + y) = _
    rw [FF_add e K he_add a b h1 h0 d u hu (w i) s 𝓡 x y, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finset.sum_coe_sort 𝓡.index _).symm
  have hcomul : ∀ F ∈ B, ∃ (m : ℕ) (F₁ F₂ : Fin m → TwFun S M → Qb),
      (∀ i, F₁ i ∈ B) ∧ (∀ i, F₂ i ∈ B) ∧ ∀ x y : TwFun S M, F (x + y) = ∑ i, F₁ i x * F₂ i y := by
    intro F hF
    obtain ⟨ι, _, F₁, F₂, hF₁, hF₂, hlaw⟩ := hcomul' hF
    let ε := Fintype.equivFin ι
    refine ⟨Fintype.card ι, fun i => F₁ (ε.symm i), fun i => F₂ (ε.symm i), fun i => hF₁ _,
      fun i => hF₂ _, fun x y => ?_⟩
    rw [hlaw x y]
    exact (Equiv.sum_comp ε.symm (fun i => F₁ i x * F₂ i y)).symm

  have hneg' : B ≤ B.comap negAlgHom := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨i, s, g⟩, rfl⟩
    rw [Subalgebra.coe_comap, Set.mem_preimage]
    have hEq : negAlgHom (p := p) (gen (i, s, g)) = FF e K (w i) s (HopfAlgebra.antipode (Rp p) (g : G)) := by
      funext x
      exact FF_neg e K he_add _ _ _ x
    rw [hEq]
    exact hmemw i s _
  have hneg : ∀ F ∈ B, (fun x => F (-x)) ∈ B := fun F hF => hneg' hF

  have hsep : ∀ x y : TwFun S M, (∀ F ∈ B, F x = F y) → x = y := by
    intro φ ψ hall
    refine TwFun.ext fun s => E_injective e fun h => ?_
    rw [E_val_eq_sum_FF e K hS a b h1 h0 s h φ, E_val_eq_sum_FF e K hS a b h1 h0 s h ψ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hall _ (hmem (a j) (ha j) s h)]

  obtain ⟨H, _, _, hHfin, hHflat, hHcomm, e', he'_add, he'_act⟩ :=
    GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure p hp B hfin hequiv hcomul hneg hsep
  refine ⟨H, _, _, hHfin, hHflat, hHcomm,
    e'.trans ⟨TwFun.val, TwFun.mk, fun _ => rfl, fun _ => rfl⟩, fun f g => ?_, fun σ f g hfg s => ?_⟩
  · change (e' (f * g)).val = (e' f).val + (e' g).val
    rw [he'_add]
    rfl
  · change (e' g).val s = σ • (e' f).val (σ⁻¹ • s)
    rw [he'_act σ f g hfg]
    rfl

end
p2m_reactivate "P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.P2mWeilRestriction.TwFun P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.P2mWeilRestriction"

end S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr
end P2MW
export P2MW.S_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr (solution)
