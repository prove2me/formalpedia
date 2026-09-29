-- Prove2me | solution 1 for GaloisRepAdic.isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ac187e51-4569-5f02-95f3-51d155887744

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Theorems.Thm_GaloisRep_exists_finiteFlat_quotient_of_equivariant_surjection
import Theorems.Thm_RibetIrr_module_finite_padicInt_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion

set_option autoImplicit false

noncomputable section

namespace LatAsm

open IsLocalRing
open scoped TensorProduct

local notation "Galℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def HasFFModel (p : ℕ) (M : Type) [AddCommGroup M] [DistribMulAction Galℚ M] : Prop :=
  ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) G),
    Module.Finite (GaloisRep.ratLocalizedAt p) G ∧ Module.Flat (GaloisRep.ratLocalizedAt p) G ∧
    Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G ∧
    ∃ e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : Galℚ) (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ x : G, g x = σ (f x)) → e g = σ • e f

theorem HasFFModel.sub {p : ℕ} {M N : Type} [AddCommGroup M] [DistribMulAction Galℚ M]
    [AddCommGroup N] [DistribMulAction Galℚ N] (h : HasFFModel p M)
    (ι : N →+ M) (hι : Function.Injective ι) (hιeq : ∀ (σ : Galℚ) (n : N), ι (σ • n) = σ • ι n) :
    HasFFModel p N := by
  obtain ⟨G, _, _, hfin, hflat, hcomm, e, hadd, hact⟩ := h
  haveI := hfin; haveI := hflat; haveI := hcomm
  obtain ⟨H, _, _, h1, h2, h3, e', h4, h5⟩ :=
    GaloisRep.exists_finiteFlat_sub_of_equivariant_injection p G e hadd hact ι hι hιeq
  exact ⟨H, _, _, h1, h2, h3, e', h4, h5⟩

theorem HasFFModel.quot {p : ℕ} {M N : Type} [AddCommGroup M] [DistribMulAction Galℚ M]
    [AddCommGroup N] [DistribMulAction Galℚ N] (h : HasFFModel p M)
    (π : M →+ N) (hπ : Function.Surjective π) (hπeq : ∀ (σ : Galℚ) (m : M), π (σ • m) = σ • π m) :
    HasFFModel p N := by
  obtain ⟨G, _, _, hfin, hflat, hcomm, e, hadd, hact⟩ := h
  haveI := hfin; haveI := hflat; haveI := hcomm
  obtain ⟨H, _, _, h1, h2, h3, e', h4, h5⟩ :=
    GaloisRep.exists_finiteFlat_quotient_of_equivariant_surjection p G e hadd hact π hπ hπeq
  exact ⟨H, _, _, h1, h2, h3, e', h4, h5⟩

section Actions

variable {G : Type*} [Monoid G]

abbrev actionOfRep {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (act : G →* Module.End R M) : DistribMulAction G M :=
  DistribMulAction.compHom M act

theorem actionOfRep_smul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (act : G →* Module.End R M) (g : G) (x : M) :
    (letI := actionOfRep act; g • x) = act g x := rfl

def quotRep {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (act : G →* Module.End R M)
    (N : Submodule R M) (hN : ∀ g, N ≤ N.comap (act g)) : G →* Module.End R (M ⧸ N) where
  toFun g := N.mapQ N (act g) (hN g)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H y => rw [Submodule.mapQ_apply, map_one]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [Module.End.mul_apply, Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply,
        map_mul]
      rfl

theorem quotRep_mk {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (act : G →* Module.End R M)
    (N : Submodule R M) (hN : ∀ g, N ≤ N.comap (act g)) (g : G) (x : M) :
    quotRep act N hN g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (act g x) := rfl

theorem smul_top_le_comap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (f : Module.End R M) : (I • ⊤ : Submodule R M) ≤ (I • ⊤ : Submodule R M).comap f := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

abbrev subAction {M : Type*} [AddCommGroup M] [DistribMulAction G M] (X : AddSubgroup M)
    (hX : ∀ (g : G) (x : M), x ∈ X → g • x ∈ X) : DistribMulAction G X where
  smul g x := ⟨g • (x : M), hX g x x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : M))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : M))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : M) (y : M))

end Actions

abbrev torsAction {J : Type} [AddCommGroup J] [DistribMulAction Galℚ J] (n : ℤ) :
    DistribMulAction Galℚ ↥(Submodule.torsionBy ℤ J n).toAddSubgroup :=
  subAction (G := Galℚ) (Submodule.torsionBy ℤ J n).toAddSubgroup (fun σ x hx => by
    change x ∈ Submodule.torsionBy ℤ J n at hx
    change σ • x ∈ Submodule.torsionBy ℤ J n
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    rw [smul_comm, hx, smul_zero])

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem exists_pow_eq_mul_of_mem_maximalIdeal {a q : R} (ha : a ≠ 0)
    (hq : q ∈ maximalIdeal R) : ∃ (c : ℕ) (b : R), q ^ c = a * b := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hq
  obtain ⟨d, rfl⟩ := hq
  refine ⟨n, ((u⁻¹ : Rˣ) : R) * d ^ n, ?_⟩
  rw [hn, mul_pow]
  calc d ^ n * ϖ ^ n = ((u : R) * (u⁻¹ : Rˣ)) * (ϖ ^ n * d ^ n) := by
          rw [Units.mul_inv, one_mul, mul_comm]
    _ = (u : R) * ϖ ^ n * ((u⁻¹ : Rˣ) * d ^ n) := by ring

theorem exists_pow_mem_of_finite_quotient [CharZero R] {q : R} (hq : q ∈ maximalIdeal R)
    (I : Ideal R) (hI : Finite (R ⧸ I)) : ∃ c : ℕ, q ^ c ∈ I := by
  have hI0 : I ≠ ⊥ := by
    intro h
    subst h
    haveI : Infinite R := Infinite.of_injective (fun n : ℕ => (n : R)) Nat.cast_injective
    have e : R ≃ R ⧸ (⊥ : Ideal R) := (RingEquiv.quotientBot R).symm.toEquiv
    exact (Infinite.of_injective e e.injective).not_finite hI
  obtain ⟨x, hxI, hx0⟩ := I.ne_bot_iff.mp hI0
  obtain ⟨c, b, hcb⟩ := exists_pow_eq_mul_of_mem_maximalIdeal hx0 hq
  exact ⟨c, hcb ▸ I.mul_mem_right b hxI⟩

end DVR

section Engine

open Submodule

variable {R : Type*} [CommRing R]

theorem exists_inf_pow_smul_le [IsNoetherianRing R] {Y : Type*} [AddCommGroup Y] [Module R Y]
    [Module.Finite R Y] (p : R) (N : Submodule R Y) (c : ℕ) :
    ∃ m : ℕ, N ⊓ (Ideal.span {p} ^ m • ⊤ : Submodule R Y) ≤ Ideal.span {p} ^ c • N := by
  obtain ⟨k, hk⟩ := (Ideal.span {p} : Ideal R).exists_pow_inf_eq_pow_smul N
  refine ⟨k + c, ?_⟩
  rw [inf_comm, hk (k + c) (Nat.le_add_right k c), Nat.add_sub_cancel_left]
  exact Submodule.smul_mono le_rfl inf_le_right

variable {G : Type*} [Monoid G]

theorem exists_stable_submodule_surjective_equivariant [IsNoetherianRing R]
    {V Y : Type*} [AddCommGroup V] [Module R V] [AddCommGroup Y] [Module R Y] [Module.Finite R Y]
    (πV : G →* Module.End R V) (πY : G →* Module.End R Y)
    (j : V →ₗ[R] Y) (hj : Function.Injective j) (hjG : ∀ g v, j (πV g v) = πY g (j v))
    (p : R) (c : ℕ) :
    ∃ (m : ℕ) (X : Submodule R (Y ⧸ (Ideal.span {p} ^ m • ⊤ : Submodule R Y)))
      (hX : ∀ (g : G) (x : Y), Submodule.Quotient.mk x ∈ X → Submodule.Quotient.mk (πY g x) ∈ X)
      (π : X →ₗ[R] V ⧸ (Ideal.span {p} ^ c • ⊤ : Submodule R V)),
      Function.Surjective π ∧
      (∀ v : V, ∃ hx : Submodule.Quotient.mk (j v) ∈ X,
        π ⟨Submodule.Quotient.mk (j v), hx⟩ = Submodule.Quotient.mk v) ∧
      ∀ (g : G) (x : Y) (hx : Submodule.Quotient.mk x ∈ X),
        π ⟨Submodule.Quotient.mk (πY g x), hX g x hx⟩ =
          Submodule.mapQ _ _ (πV g) (by
            rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
            exact Submodule.smul_mono le_rfl le_top) (π ⟨Submodule.Quotient.mk x, hx⟩) := by
  classical
  set N : Submodule R Y := LinearMap.range j with hN
  obtain ⟨m, hm⟩ := exists_inf_pow_smul_le p N c
  set PmY : Submodule R Y := Ideal.span {p} ^ m • ⊤ with hPmY
  set PcV : Submodule R V := Ideal.span {p} ^ c • ⊤ with hPcV

  let X : Submodule R (Y ⧸ PmY) := N.map PmY.mkQ

  have hkey : ∀ v : V, j v ∈ PmY → v ∈ PcV := by
    intro v hv
    have hmem : j v ∈ N ⊓ PmY := ⟨LinearMap.mem_range_self j v, hv⟩
    have h2 : j v ∈ Ideal.span {p} ^ c • N := hm hmem
    have h3 : Ideal.span {p} ^ c • N = (Ideal.span {p} ^ c • (⊤ : Submodule R V)).map j := by
      rw [hN, ← Submodule.map_top, Submodule.map_smul'']
    rw [h3] at h2
    obtain ⟨w, hw, hjw⟩ := h2
    have : w = v := hj hjw
    rw [← this]; exact hw

  have hpre : ∀ y : N, ∃ v : V, j v = y := fun y => by
    obtain ⟨v, hv⟩ := y.2; exact ⟨v, hv⟩
  let lift : N → V := fun y => (hpre y).choose
  have hlift : ∀ y : N, j (lift y) = y := fun y => (hpre y).choose_spec
  have hlift_eq : ∀ (v : V), lift ⟨j v, LinearMap.mem_range_self j v⟩ = v :=
    fun v => hj (hlift _)
  let φ₀ : N →ₗ[R] V :=
    { toFun := lift
      map_add' := fun x y => hj (by rw [hlift, map_add, hlift, hlift]; rfl)
      map_smul' := fun r x => hj (by rw [hlift, map_smul, hlift]; rfl) }
  have hφ₀ : ∀ v : V, φ₀ ⟨j v, LinearMap.mem_range_self j v⟩ = v := hlift_eq
  let φ : N →ₗ[R] V ⧸ PcV := PcV.mkQ.comp φ₀

  have hφker : ∀ y : N, (y : Y) ∈ PmY → φ y = 0 := by
    intro y hy
    obtain ⟨v, hv⟩ := hpre y
    have : y = ⟨j v, LinearMap.mem_range_self j v⟩ := Subtype.ext hv.symm
    subst this
    show PcV.mkQ (φ₀ ⟨j v, _⟩) = 0
    rw [hφ₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hkey v hy

  have hXmem : ∀ x : X, ∃ y : N, PmY.mkQ (y : Y) = (x : Y ⧸ PmY) := by
    intro x
    obtain ⟨y, hyN, hy⟩ := x.2
    exact ⟨⟨y, hyN⟩, hy⟩
  let ψ : X → V ⧸ PcV := fun x => φ (hXmem x).choose
  have hψ : ∀ (x : X) (y : N), PmY.mkQ (y : Y) = (x : Y ⧸ PmY) → ψ x = φ y := by
    intro x y hy
    have h1 := (hXmem x).choose_spec
    have hdiff : ((hXmem x).choose : Y) - (y : Y) ∈ PmY := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, h1, hy]
    have := hφker ((hXmem x).choose - y) hdiff
    rw [map_sub, sub_eq_zero] at this
    exact this
  let π : X →ₗ[R] V ⧸ PcV :=
    { toFun := ψ
      map_add' := by
        intro a b
        obtain ⟨ya, hya⟩ := hXmem a
        obtain ⟨yb, hyb⟩ := hXmem b
        rw [hψ a ya hya, hψ b yb hyb, hψ (a + b) (ya + yb) (by
          rw [Submodule.coe_add, map_add, hya, hyb]; rfl), map_add]
      map_smul' := by
        intro r a
        obtain ⟨ya, hya⟩ := hXmem a
        rw [hψ a ya hya, hψ (r • a) (r • ya) (by
          rw [Submodule.coe_smul, map_smul, hya]; rfl), map_smul]; rfl }
  have hπj : ∀ v : V, ∀ (hx : PmY.mkQ (j v) ∈ X),
      π ⟨PmY.mkQ (j v), hx⟩ = PcV.mkQ v := by
    intro v hx
    show ψ _ = _
    rw [hψ ⟨PmY.mkQ (j v), hx⟩ ⟨j v, LinearMap.mem_range_self j v⟩ rfl]
    show PcV.mkQ (φ₀ ⟨j v, _⟩) = _
    rw [hφ₀]

  have hpres : ∀ (g : G), ∀ z ∈ PmY, πY g z ∈ PmY := by
    intro g z hz
    have : PmY.map (πY g) ≤ PmY := by
      rw [hPmY, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨z, hz, rfl⟩
  have hXstab : ∀ (g : G) (x : Y), Submodule.Quotient.mk x ∈ X →
      Submodule.Quotient.mk (πY g x) ∈ X := by
    intro g x hx
    obtain ⟨y, hyN, hy⟩ := hx
    obtain ⟨v, rfl⟩ := hyN
    have hdiff : x - j v ∈ PmY := by
      rw [← Submodule.Quotient.eq]; exact hy.symm
    have h1 : Submodule.Quotient.mk (p := PmY) (πY g x) = Submodule.Quotient.mk (πY g (j v)) := by
      rw [Submodule.Quotient.eq, ← map_sub]
      exact hpres g _ hdiff
    rw [h1, ← hjG]
    exact ⟨j (πV g v), LinearMap.mem_range_self j _, rfl⟩
  refine ⟨m, X, hXstab, π, ?_, ?_, ?_⟩
  ·
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H v =>
      exact ⟨⟨PmY.mkQ (j v), ⟨j v, LinearMap.mem_range_self j v, rfl⟩⟩, hπj v _⟩
  ·
    intro v
    exact ⟨⟨j v, LinearMap.mem_range_self j v, rfl⟩, hπj v _⟩
  ·
    intro g x hx
    obtain ⟨y, hyN, hy⟩ := id hx
    obtain ⟨v, rfl⟩ := hyN
    have hdiff : x - j v ∈ PmY := by
      rw [← Submodule.Quotient.eq]; exact hy.symm
    have hx' : (Submodule.Quotient.mk x : Y ⧸ PmY) = PmY.mkQ (j v) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]; exact hdiff
    have hgx' : (Submodule.Quotient.mk (πY g x) : Y ⧸ PmY) = PmY.mkQ (j (πV g v)) := by
      rw [hjG, Submodule.mkQ_apply, Submodule.Quotient.eq, ← map_sub]; exact hpres g _ hdiff
    have e1 : (⟨Submodule.Quotient.mk (πY g x), hXstab g x hx⟩ : X) =
        ⟨PmY.mkQ (j (πV g v)), ⟨j (πV g v), LinearMap.mem_range_self j _, rfl⟩⟩ :=
      Subtype.ext hgx'
    have e2 : (⟨Submodule.Quotient.mk x, hx⟩ : X) =
        ⟨PmY.mkQ (j v), ⟨j v, LinearMap.mem_range_self j v, rfl⟩⟩ := Subtype.ext hx'
    rw [e1, e2, hπj, hπj]
    rfl

end Engine

section Main

variable (p : ℕ) [Fact p.Prime]
  {J : Type} [AddCommGroup J] [DistribMulAction Galℚ J]

def levelPi (m r : ℕ) :
    (Fin r → TateModule p J) →+ (Fin r → ↥(Submodule.torsionBy ℤ J ((p ^ m : ℕ) : ℤ)).toAddSubgroup) where
  toFun x i := ⟨TateModule.proj p J m (x i), TateModule.proj_mem_torsionBy m (x i)⟩
  map_zero' := by ext i; rfl
  map_add' x y := by ext i; rfl

omit [Fact p.Prime] [DistribMulAction Galℚ J] in
theorem levelPi_apply_coe (m r : ℕ) (x : Fin r → TateModule p J) (i : Fin r) :
    ((levelPi p m r x i : ↥(Submodule.torsionBy ℤ J ((p ^ m : ℕ) : ℤ)).toAddSubgroup) : J) =
      ((x i : TateModule p J) : ℕ → J) m := rfl

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main
    [Module.Finite ℤ_[p] (TateModule p J)]
    (hJ : ∀ n b : ℕ,
      ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) G),
        Module.Finite (GaloisRep.ratLocalizedAt p) G ∧ Module.Flat (GaloisRep.ratLocalizedAt p) G ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G ∧
        ∃ e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
            (Fin b → ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup),
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : Galℚ) (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : G, g x = σ (f x)) →
              ∀ i : Fin b,
                ((e g i : ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup) : J) =
                  σ • ((e f i : ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup) : J))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [CharZero O] [Algebra ℤ_[p] O]
    (hpO : (p : O) ∈ maximalIdeal O)
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] O K]
    (ρ : GaloisRepAdic O)
    (π : K ⊗[ℤ_[p]] TateModule p J →ₗ[K] K ⊗[O] ρ.V) (hπ : Function.Surjective π)
    (hπeq : ∀ (σ : Galℚ) (x : K ⊗[ℤ_[p]] TateModule p J),
      π ((TateModule.rep p J Galℚ σ).baseChange K x) = (ρ.ρ σ).baseChange K (π x)) :
    ρ.IsFlatAt p := by
  classical
  refine ⟨‹Finite (ResidueField O)›, fun I hIfin => ?_⟩

  set T := TateModule p J with hTdef
  set V := ρ.V with hVdef

  haveI : IsScalarTower O K (K ⊗[O] V) := TensorProduct.isScalarTower_left
  haveI : IsScalarTower ℤ_[p] K (K ⊗[O] V) := TensorProduct.isScalarTower_left
  haveI : IsScalarTower ℤ_[p] O (K ⊗[O] V) := TensorProduct.isScalarTower_left
  haveI : IsScalarTower ℤ_[p] K (K ⊗[ℤ_[p]] T) := TensorProduct.isScalarTower_left
  haveI : IsNoetherianRing O := inferInstance
  have hinjOK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hp0 : (p : O) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  let ρK : Galℚ →* Module.End K (K ⊗[O] V) :=
    (Module.End.baseChangeHom O K V).toMonoidHom.comp ρ.ρ
  have ρK_apply : ∀ σ : Galℚ, ρK σ = (ρ.ρ σ).baseChange K := fun _ => rfl
  let repT : Galℚ →* Module.End ℤ_[p] T := TateModule.rep p J Galℚ
  let repK : Galℚ →* Module.End K (K ⊗[ℤ_[p]] T) :=
    (Module.End.baseChangeHom ℤ_[p] K T).toMonoidHom.comp repT
  have repK_apply : ∀ σ : Galℚ, repK σ = (repT σ).baseChange K := fun _ => rfl

  let φ₀ : T →ₗ[ℤ_[p]] K ⊗[O] V :=
    (π.restrictScalars ℤ_[p]).comp (TensorProduct.mk ℤ_[p] K T 1)
  have φ₀_apply : ∀ t : T, φ₀ t = π (1 ⊗ₜ t) := fun _ => rfl
  have φ₀_equiv : ∀ (σ : Galℚ) (t : T), φ₀ (repT σ t) = ρK σ (φ₀ t) := by
    intro σ t
    rw [φ₀_apply, φ₀_apply, ρK_apply, ← hπeq σ, LinearMap.baseChange_tmul]
  let Ψ : O ⊗[ℤ_[p]] T →ₗ[O] K ⊗[O] V := φ₀.liftBaseChange O
  have Ψ_tmul : ∀ (o : O) (t : T), Ψ (o ⊗ₜ t) = o • φ₀ t := fun o t => LinearMap.liftBaseChange_tmul _ _ _ _
  let Y : Submodule O (K ⊗[O] V) := LinearMap.range Ψ
  letI : AddCommGroup ↥Y := Y.addCommGroup
  letI : Module O ↥Y := Y.module
  haveI : Module.Finite O Y := inferInstance

  have hYstab : ∀ (σ : Galℚ), ∀ y ∈ Y, ρK σ y ∈ Y := by
    intro σ y hy
    obtain ⟨w, rfl⟩ := hy
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact Y.zero_mem
    | tmul o t =>
      refine ⟨o ⊗ₜ repT σ t, ?_⟩
      rw [Ψ_tmul, Ψ_tmul, φ₀_equiv, LinearMap.map_smul_of_tower]
    | add x y hx hy => rw [map_add, map_add]; exact Y.add_mem hx hy
  let πY : Galℚ →* Module.End O Y :=
    { toFun := fun σ => ((ρK σ).restrictScalars O).restrict (hYstab σ)
      map_one' := by
        refine LinearMap.ext fun y => Subtype.ext ?_
        show ρK 1 y = y
        rw [map_one]; rfl
      map_mul' := fun σ τ => by
        refine LinearMap.ext fun y => Subtype.ext ?_
        show ρK (σ * τ) y = ρK σ (ρK τ y)
        rw [map_mul]; rfl }
  have πY_apply_coe : ∀ (σ : Galℚ) (y : Y), ((πY σ y : Y) : K ⊗[O] V) = ρK σ y := fun _ _ => rfl

  let ιV : V →ₗ[O] K ⊗[O] V := TensorProduct.mk O K V 1
  have ιV_apply : ∀ v : V, ιV v = 1 ⊗ₜ v := fun _ => rfl

  let ι0 := Module.Free.ChooseBasisIndex O V
  let bV : Module.Basis ι0 O V := Module.Free.chooseBasis O V
  haveI : Fintype ι0 := inferInstance
  let bE := Algebra.TensorProduct.basis K bV
  have hιV_inj : Function.Injective ιV := by
    intro v w hvw
    rw [← sub_eq_zero]
    have h0 : ιV (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    set u := v - w
    have hrepr : ∀ i, algebraMap O K (bV.repr u i) = 0 := by
      intro i
      have := congrArg (fun z => bE.repr z i) h0
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      rw [← this, ιV_apply]
      rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
    have : bV.repr u = 0 :=
      Finsupp.ext fun i => hinjOK (by rw [hrepr i, Finsupp.coe_zero, Pi.zero_apply, map_zero])
    exact bV.repr.injective (by rw [this, map_zero])
  have ιV_equiv : ∀ (σ : Galℚ) (v : V), ιV (ρ.ρ σ v) = ρK σ (ιV v) := by
    intro σ v
    rw [ιV_apply, ιV_apply, ρK_apply, LinearMap.baseChange_tmul]

  have hspanY : Submodule.span K (Y : Set (K ⊗[O] V)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := hπ z
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul k t =>
      have : (k ⊗ₜ[ℤ_[p]] t : K ⊗[ℤ_[p]] T) = k • (1 ⊗ₜ t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul]
      refine Submodule.smul_mem _ k (Submodule.subset_span ?_)
      refine ⟨(1 : O) ⊗ₜ t, ?_⟩
      rw [Ψ_tmul, one_smul]
      rfl
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ (hx trivial) (hy trivial)

  have hden : ∀ z : K ⊗[O] V, ∃ d : O, d ≠ 0 ∧ (algebraMap O K d) • z ∈ Y := by
    intro z
    have hz : z ∈ Submodule.span K (Y : Set (K ⊗[O] V)) := by rw [hspanY]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_ne_zero, by rw [map_one, one_smul]; exact hy⟩
    | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Y.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨d₁, hd₁, hx⟩ := hx
      obtain ⟨d₂, hd₂, hy⟩ := hy
      refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
      rw [smul_add, map_mul]
      refine Y.add_mem ?_ ?_
      · rw [mul_comm, mul_smul, algebraMap_smul]
        exact Y.smul_mem d₂ hx
      · rw [mul_smul, algebraMap_smul]
        exact Y.smul_mem d₁ hy
    | smul k x _ hx =>
      obtain ⟨d, hd, hx⟩ := hx
      obtain ⟨⟨o, s⟩, hos⟩ := IsLocalization.surj (nonZeroDivisors O) k
      refine ⟨(s : O) * d, mul_ne_zero (nonZeroDivisors.ne_zero s.2) hd, ?_⟩
      have hk : ∀ z : K ⊗[O] V, algebraMap O K (s : O) • (k • z) = (o : O) • z := by
        intro z
        rw [← mul_smul, mul_comm, hos, algebraMap_smul]
      rw [map_mul, mul_smul, smul_comm (algebraMap O K d), hk]
      exact Y.smul_mem o hx

  have hpow : ∃ a : ℕ, ∀ v : V, ((p : O) ^ a) • ιV v ∈ Y := by
    have hb : ∀ i : ι0, ∃ d : O, d ≠ 0 ∧ (algebraMap O K d) • ιV (bV i) ∈ Y := fun i => hden _
    choose d hd0 hd using hb
    let D : O := ∏ i, d i
    have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hd0 i
    have hD : ∀ i, D • ιV (bV i) ∈ Y := by
      intro i
      obtain ⟨c, hc⟩ : d i ∣ D := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
      rw [hc, mul_comm, mul_smul, ← algebraMap_smul K (d i)]
      exact Y.smul_mem c (hd i)
    obtain ⟨a, b, hab⟩ := exists_pow_eq_mul_of_mem_maximalIdeal hD0 hpO
    refine ⟨a, fun v => ?_⟩
    have hv : v = ∑ i, bV.repr v i • bV i := (bV.sum_repr v).symm
    rw [hv, map_sum, Finset.smul_sum]
    refine Y.sum_mem fun i _ => ?_
    rw [map_smul, smul_comm, hab, mul_comm, mul_smul]
    exact Y.smul_mem _ (Y.smul_mem _ (hD i))
  obtain ⟨a, ha⟩ := hpow

  let j : V →ₗ[O] Y :=
    { toFun := fun v => ⟨((p : O) ^ a) • ιV v, ha v⟩
      map_add' := fun v w => Subtype.ext (by
        show ((p : O) ^ a) • ιV (v + w) = ((p : O) ^ a) • ιV v + ((p : O) ^ a) • ιV w
        rw [map_add, smul_add])
      map_smul' := fun o v => Subtype.ext (by
        show ((p : O) ^ a) • ιV (o • v) = o • (((p : O) ^ a) • ιV v)
        rw [map_smul, smul_comm]) }
  have j_apply_coe : ∀ v : V, ((j v : Y) : K ⊗[O] V) = ((p : O) ^ a) • ιV v := fun _ => rfl
  have hj_inj : Function.Injective j := by
    intro v w hvw
    have h1 : ((p : O) ^ a) • ιV v = ((p : O) ^ a) • ιV w := congrArg (fun y : Y => (y : K ⊗[O] V)) hvw
    rw [← algebraMap_smul K ((p : O) ^ a), ← algebraMap_smul K ((p : O) ^ a)] at h1
    have hne : algebraMap O K ((p : O) ^ a) ≠ 0 := by
      rw [map_ne_zero_iff _ hinjOK]; exact pow_ne_zero _ hp0
    exact hιV_inj (smul_right_injective _ hne h1)
  have hjG : ∀ (σ : Galℚ) (v : V), j (ρ.ρ σ v) = πY σ (j v) := by
    intro σ v
    refine Subtype.ext ?_
    rw [j_apply_coe, πY_apply_coe, j_apply_coe, ιV_equiv, LinearMap.map_smul_of_tower]

  obtain ⟨c, hcI⟩ := exists_pow_mem_of_finite_quotient hpO I hIfin
  obtain ⟨m, X, hXstab, πX, hπXsurj, hπXj, hπXeq⟩ :=
    exists_stable_submodule_surjective_equivariant (R := O) (G := Galℚ) (V := V) (Y := ↥Y)
      (πV := ρ.ρ) (πY := πY) (j := j) hj_inj hjG (p : O) c
  have hPcV_le : (Ideal.span {(p : O)} ^ c • ⊤ : Submodule O V) ≤ (I • ⊤ : Submodule O V) := by
    refine Submodule.smul_mono ?_ le_rfl
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hcI

  haveI : Module.Finite ℤ_[p] O := RibetIrr.module_finite_padicInt_of_isDiscreteValuationRing p O hpO
  obtain ⟨r, og, hog⟩ := Module.Finite.exists_fin (R := ℤ_[p]) (M := O)

  let Φ₀ : (Fin r → T) →ₗ[ℤ_[p]] K ⊗[O] V :=
    ∑ i : Fin r, ((og i) • φ₀).comp (LinearMap.proj i)
  have Φ₀_apply : ∀ x : Fin r → T, Φ₀ x = ∑ i, og i • φ₀ (x i) := by
    intro x
    simp only [Φ₀, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.smul_apply]
  have hΦ₀_mem : ∀ x, Φ₀ x ∈ Y := by
    intro x
    rw [Φ₀_apply]
    refine Y.sum_mem fun i _ => ⟨og i ⊗ₜ x i, ?_⟩
    rw [Ψ_tmul]
  have hΦ₀_surj : ∀ y ∈ Y, ∃ x, Φ₀ x = y := by
    intro y hy
    obtain ⟨w, rfl⟩ := hy
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul o t =>

      have ho : o ∈ Submodule.span ℤ_[p] (Set.range og) := by rw [hog]; exact Submodule.mem_top
      obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp ho
      refine ⟨fun i => cf i • t, ?_⟩
      rw [Φ₀_apply, Ψ_tmul, ← hcf, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_comm, ← smul_assoc]
    | add x y hx hy =>
      obtain ⟨x₁, hx₁⟩ := hx
      obtain ⟨y₁, hy₁⟩ := hy
      exact ⟨x₁ + y₁, by rw [map_add, hx₁, hy₁, map_add]⟩
  let Φ : (Fin r → T) →ₗ[ℤ_[p]] Y := LinearMap.codRestrict (Y.restrictScalars ℤ_[p]) Φ₀ hΦ₀_mem
  have Φ_apply_coe : ∀ x, ((Φ x : Y) : K ⊗[O] V) = Φ₀ x := fun _ => rfl
  have hΦsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨x, hx⟩ := hΦ₀_surj y y.2
    exact ⟨x, Subtype.ext hx⟩

  let repPi : Galℚ →* Module.End ℤ_[p] (Fin r → T) :=
    { toFun := fun σ => LinearMap.pi fun i => (repT σ).comp (LinearMap.proj i)
      map_one' := by ext x i; simp
      map_mul' := fun σ τ => by ext x i; simp }
  have repPi_apply : ∀ (σ : Galℚ) (x : Fin r → T) (i : Fin r), repPi σ x i = repT σ (x i) :=
    fun _ _ _ => rfl
  have hΦG : ∀ (σ : Galℚ) (x : Fin r → T), Φ (repPi σ x) = πY σ (Φ x) := by
    intro σ x
    refine Subtype.ext ?_
    rw [Φ_apply_coe, πY_apply_coe, Φ_apply_coe, Φ₀_apply, Φ₀_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repPi_apply, φ₀_equiv, LinearMap.map_smul_of_tower]

  let N₀ : Submodule ℤ_[p] (Fin r → T) :=
    Submodule.pi Set.univ fun _ => (maximalIdeal ℤ_[p] ^ m • ⊤ : Submodule ℤ_[p] T)
  have hN₀ : ∀ x : Fin r → T, x ∈ N₀ ↔ ∀ i, TateModule.proj p J m (x i) = 0 := by
    intro x
    simp only [N₀, Submodule.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun i => (TateModule.proj_eq_zero_iff m (x i)).symm
  have hN₀stab : ∀ σ : Galℚ, N₀ ≤ N₀.comap (repPi σ) := by
    intro σ x hx
    rw [Submodule.mem_comap, hN₀]
    rw [hN₀] at hx
    intro i
    rw [repPi_apply]
    have h1 := hx i
    rw [TateModule.proj_apply] at h1 ⊢
    rw [TateModule.rep_apply, h1, smul_zero]

  have hN₀Φ : ∀ x ∈ N₀, (Submodule.Quotient.mk (Φ x) :
      Y ⧸ (Ideal.span {(p : O)} ^ m • ⊤ : Submodule O Y)) = 0 := by
    intro x hx
    rw [Submodule.Quotient.mk_eq_zero]

    rw [hN₀] at hx
    have hxi : ∀ i, ∃ s : T, ((p : ℤ_[p]) ^ m) • s = x i := fun i =>
      ⟨TateModule.shiftOfProjEqZero m (x i) (hx i), TateModule.pow_smul_shiftOfProjEqZero m (x i) (hx i)⟩
    choose s hs using hxi
    have hx' : x = ((p : ℤ_[p]) ^ m) • (fun i => s i) := by
      funext i; rw [Pi.smul_apply, hs]
    rw [hx', map_smul]
    have : ((p : ℤ_[p]) ^ m) • Φ (fun i => s i) = ((p : O) ^ m) • Φ (fun i => s i) := by
      rw [← algebraMap_smul O ((p : ℤ_[p]) ^ m), map_pow, map_natCast]
    rw [this]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
  let B := (Fin r → T) ⧸ N₀
  let ΦB : B →ₗ[ℤ_[p]] Y ⧸ (Ideal.span {(p : O)} ^ m • ⊤ : Submodule O Y) :=
    N₀.liftQ (((Ideal.span {(p : O)} ^ m • ⊤ : Submodule O Y).mkQ.restrictScalars ℤ_[p]).comp Φ)
      (fun x hx => LinearMap.mem_ker.mpr (hN₀Φ x hx))
  have ΦB_mk : ∀ x : Fin r → T, ΦB (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Φ x) :=
    fun _ => rfl
  have hΦBsurj : Function.Surjective ΦB := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x, rfl⟩ := hΦsurj y
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  let repB : Galℚ →* Module.End ℤ_[p] B := quotRep repPi N₀ hN₀stab

  let A := Fin r → ↥(Submodule.torsionBy ℤ J ((p ^ m : ℕ) : ℤ)).toAddSubgroup
  have hlevker : ∀ x : Fin r → T, x ∈ N₀ ↔ levelPi p m r x = 0 := by
    intro x
    rw [hN₀]
    constructor
    · intro h; funext i; exact Subtype.ext (h i)
    · intro h i; exact congrArg (fun y : A => ((y i : _) : J)) h
  let levB : B →+ A :=
    QuotientAddGroup.lift N₀.toAddSubgroup (levelPi p m r)
      (fun x hx => (AddMonoidHom.mem_ker).mpr ((hlevker x).mp hx))
  have levB_mk : ∀ x : Fin r → T, levB (Submodule.Quotient.mk x) = levelPi p m r x := fun _ => rfl
  have hlevB_inj : Function.Injective levB := by
    intro x y hxy
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        rw [levB_mk, levB_mk, ← sub_eq_zero, ← map_sub] at hxy
        rw [Submodule.Quotient.eq]
        exact (hlevker _).mpr hxy

  letI iTors : DistribMulAction Galℚ ↥(Submodule.torsionBy ℤ J ((p ^ m : ℕ) : ℤ)).toAddSubgroup :=
    torsAction ((p ^ m : ℕ) : ℤ)
  letI iA : DistribMulAction Galℚ A := Pi.distribMulAction _
  have hA : HasFFModel p A := by
    obtain ⟨G, iG, iH, h1, h2, h3, e, h4, h5⟩ := hJ m r
    refine ⟨G, iG, iH, h1, h2, h3, e, h4, fun σ f g hfg => ?_⟩
    funext i
    exact Subtype.ext (h5 σ f g hfg i)

  letI iB : DistribMulAction Galℚ B := actionOfRep repB
  have iB_smul : ∀ (σ : Galℚ) (x : Fin r → T),
      (σ • (Submodule.Quotient.mk x : B)) = Submodule.Quotient.mk (repPi σ x) := fun _ _ => rfl
  let Xt : AddSubgroup B := (X.toAddSubgroup).comap ΦB.toAddMonoidHom
  have hXt : ∀ b : B, b ∈ Xt ↔ ΦB b ∈ X := fun _ => Iff.rfl
  have hXtstab : ∀ (σ : Galℚ) (b : B), b ∈ Xt → σ • b ∈ Xt := by
    intro σ b hb
    induction b using Submodule.Quotient.induction_on with
    | H x =>
      rw [hXt, ΦB_mk] at hb
      rw [iB_smul, hXt, ΦB_mk, hΦG]
      exact hXstab σ (Φ x) hb
  letI iXt : DistribMulAction Galℚ Xt := subAction Xt hXtstab
  have iXt_smul : ∀ (σ : Galℚ) (x : Xt), ((σ • x : Xt) : B) = σ • (x : B) := fun _ _ => rfl
  have hXtff : HasFFModel p Xt := by
    refine hA.sub (levB.comp Xt.subtype) (fun x y h => Subtype.ext (hlevB_inj h)) (fun σ x => ?_)
    obtain ⟨b, hb⟩ := x
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddSubgroup.subtype_apply,
      AddSubgroup.subtype_apply, iXt_smul]
    induction b using Submodule.Quotient.induction_on with
    | H z =>
      rw [iB_smul, levB_mk, levB_mk]
      funext i
      exact Subtype.ext rfl

  let IV : Submodule O V := I • ⊤
  let repIV : Galℚ →* Module.End O (V ⧸ IV) := quotRep ρ.ρ IV (fun σ => smul_top_le_comap I (ρ.ρ σ))
  letI iIV : DistribMulAction Galℚ (V ⧸ IV) := actionOfRep repIV
  have iIV_smul : ∀ (σ : Galℚ) (q : V ⧸ IV), σ • q = ρ.levelAction I σ q := fun _ _ => rfl
  let toIV : (V ⧸ (Ideal.span {(p : O)} ^ c • ⊤ : Submodule O V)) →ₗ[O] V ⧸ IV :=
    Submodule.mapQ _ IV LinearMap.id (by rw [Submodule.comap_id]; exact hPcV_le)
  have toIV_mk : ∀ v : V, toIV (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun _ => rfl
  let toX : Xt →+ X :=
    { toFun := fun x => ⟨ΦB (x : B), (hXt x).mp x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have toX_apply_coe : ∀ x : Xt, ((toX x : X) : Y ⧸ (Ideal.span {(p : O)} ^ m • ⊤ : Submodule O Y)) =
      ΦB (x : B) := fun _ => rfl
  let πXt : Xt →+ V ⧸ IV := toIV.toAddMonoidHom.comp (πX.toAddMonoidHom.comp toX)
  have πXt_apply : ∀ x : Xt, πXt x = toIV (πX (toX x)) := fun _ => rfl
  have hπXt_surj : Function.Surjective πXt := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H v =>
      obtain ⟨ξ, hξ⟩ := hπXsurj (Submodule.Quotient.mk v)
      obtain ⟨b, hb⟩ := hΦBsurj (ξ : Y ⧸ (Ideal.span {(p : O)} ^ m • ⊤ : Submodule O Y))
      have hbX : b ∈ Xt := by rw [hXt, hb]; exact ξ.2
      refine ⟨⟨b, hbX⟩, ?_⟩
      rw [πXt_apply]
      have : toX ⟨b, hbX⟩ = ξ := Subtype.ext hb
      rw [this, hξ, toIV_mk]
  have hπXt_eq : ∀ (σ : Galℚ) (x : Xt), πXt (σ • x) = σ • πXt x := by
    intro σ x
    obtain ⟨b, hb⟩ := x
    induction b using Submodule.Quotient.induction_on with
    | H z =>
      have hzX : Submodule.Quotient.mk (Φ z) ∈ X := by
        have := (hXt _).mp hb
        rwa [ΦB_mk] at this

      have hl : toX (σ • ⟨Submodule.Quotient.mk z, hb⟩) =
          ⟨Submodule.Quotient.mk (πY σ (Φ z)), hXstab σ (Φ z) hzX⟩ := by
        refine Subtype.ext ?_
        rw [toX_apply_coe, iXt_smul]
        show ΦB (σ • (Submodule.Quotient.mk z : B)) = _
        rw [iB_smul, ΦB_mk, hΦG]
      have hr : toX ⟨Submodule.Quotient.mk z, hb⟩ = ⟨Submodule.Quotient.mk (Φ z), hzX⟩ :=
        Subtype.ext (by rw [toX_apply_coe]; rfl)
      rw [πXt_apply, πXt_apply, hl, hr, hπXeq σ (Φ z) hzX, iIV_smul]
      generalize πX ⟨Submodule.Quotient.mk (Φ z), hzX⟩ = q
      induction q using Submodule.Quotient.induction_on with
      | H v => rfl
  have hIVff : HasFFModel p (V ⧸ IV) := hXtff.quot πXt hπXt_surj hπXt_eq
  obtain ⟨G, iG, iH, h1, h2, h3, e, h4, h5⟩ := hIVff
  exact ⟨G, iG, iH, h1, h2, h3, e, h4, fun σ f g hfg => (h5 σ f g hfg).trans (iIV_smul σ (e f))⟩

end Main

end LatAsm

end

open IsLocalRing in
open scoped TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [Module.Finite ℤ_[p] (TateModule p J)]

    (hJ : ∀ n b : ℕ,
      ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) G),
        Module.Finite (GaloisRep.ratLocalizedAt p) G ∧ Module.Flat (GaloisRep.ratLocalizedAt p) G ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G ∧
        ∃ e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
            (Fin b → ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup),
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : G, g x = σ (f x)) →
              ∀ i : Fin b,
                ((e g i : ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup) : J) =
                  σ • ((e f i : ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup) : J))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [CharZero O] [Algebra ℤ_[p] O]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] O K]

    (ρ : GaloisRepAdic O)
    (π : K ⊗[ℤ_[p]] TateModule p J →ₗ[K] K ⊗[O] ρ.V) (hπ : Function.Surjective π)
    (hπeq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : K ⊗[ℤ_[p]] TateModule p J),
      π ((TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K x) =
        (ρ.ρ σ).baseChange K (π x)) :
    ρ.IsFlatAt p :=
  LatAsm.main p hJ O hpO K ρ π hπ hπeq

end S_GaloisRepAdic_isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion
end P2MW
export P2MW.S_GaloisRepAdic_isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion (solution)
