-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/985a9220-84cc-5787-9184-71674ca8041f

import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld.Mumford ModularCurve"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "DegeneracyData ribbonKernel HeckeData heckeKernelMap"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "PeriodDatum.coeffMap_apply PeriodDatum.precomp_apply PeriodUniformization PeriodDatum unitsBaseChange_apply PeriodDatum.QL_apply"
namespace FrobLaws
p2m_open "CerednikDrinfeld.Mumford CerednikDrinfeld"

scoped instance isometric_fact (A : ValuationSubring (AlgebraicClosure ℚ)) : Fact (A.DecompositionIsometric ℚ) :=
  ⟨fun σ x => ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A σ.2 x⟩

theorem exists_algEquiv_eq_smul (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) :
    ∃ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, ∀ c, s c = σ • c := by
  let e : A.valuation.Completion ≃+* A.valuation.Completion :=
    MulSemiringAction.toRingEquiv (A.decompositionSubgroup ℚ) A.valuation.Completion σ
  refine ⟨AlgEquiv.ofRingEquiv (f := e) (fun q => ?_), fun c => rfl⟩
  rw [Algebra.algebraMap_eq_smul_one, map_rat_smul, map_one]

section Roots

variable (A : ValuationSubring (AlgebraicClosure ℚ))

def ι : AlgebraicClosure ℚ →+* A.valuation.Completion :=
  (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).comp (WithVal.equiv A.valuation).symm.toRingHom

theorem ι_apply (x : AlgebraicClosure ℚ) : ι A x = ((x : AlgebraicClosure ℚ) : A.valuation.Completion) := rfl

theorem ι_injective : Function.Injective (ι A) := (ι A).injective

variable {A}

theorem mem_of_pow_eq_one {p : ℕ} (hp : p ≠ 0) {x : AlgebraicClosure ℚ} (hx : x ^ p = 1) : x ∈ A := by
  apply A.mem_of_valuation_le_one
  by_contra h
  have h1 : 1 < A.valuation x := lt_of_not_ge h
  have := one_lt_pow₀ h1 (n := p) hp
  rw [← map_pow, hx, map_one] at this
  exact lt_irrefl _ this

theorem residue_natCast_ne_zero {r : ℕ} [Fact r.Prime] (hA : A.LiesOverPrime r) {p : ℕ} (hp : p.Prime) (hpr : p ≠ r) :
    (p : IsLocalRing.ResidueField ↥A) ≠ 0 := by
  intro h
  rw [← map_natCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff] at h
  have hr : ((r : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have : ((r : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
    rw [ValuationSubring.mem_nonunits_iff] at this
    simpa using this
  have hcop : Nat.Coprime r p := (Nat.coprime_primes Fact.out hp).2 (Ne.symm hpr)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have hab' : (a : ↥A) * ((r : ℕ) : ↥A) + (b : ↥A) * ((p : ℕ) : ↥A) = 1 := by exact_mod_cast hab
    rw [← hab']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hr) (Ideal.mul_mem_left _ _ h)
  exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem eq_of_pow_eq_one_of_residue_eq {r : ℕ} [Fact r.Prime] (hA : A.LiesOverPrime r) {p : ℕ} (hp : p.Prime)
    (hpr : p ≠ r) {a b : ↥A} (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hab : IsLocalRing.residue ↥A a = IsLocalRing.residue ↥A b) : a = b := by

  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  set c : ↥A := a * b ^ (p - 1) with hc
  have hcb : c * b = a := by
    rw [hc, mul_assoc, ← pow_succ, hp1, hb, mul_one]
  have hcp : c ^ p = 1 := by
    rw [hc, mul_pow, ← pow_mul, ha, one_mul, mul_comm, pow_mul, hb, one_pow]
  have hres : IsLocalRing.residue ↥A c = 1 := by
    have hbres : IsLocalRing.residue ↥A b ^ p = 1 := by rw [← map_pow, hb, map_one]
    rw [hc, map_mul, map_pow, hab, ← pow_succ', hp1, hbres]

  have hgeom : (c - 1) * (Finset.range p).sum (fun i => c ^ i) = 0 := by
    rw [mul_geom_sum, hcp, sub_self]
  have hunit : (Finset.range p).sum (fun i => c ^ i) ≠ 0 := by
    intro h0
    apply residue_natCast_ne_zero hA hp hpr
    have := congrArg (IsLocalRing.residue ↥A) h0
    rw [map_sum, map_zero] at this
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    exact this
  have hc1 : c = 1 := by
    rcases mul_eq_zero.1 hgeom with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hunit
  rw [← hcb, hc1, one_mul]

theorem frob_apply_eq_pow {r : ℕ} [Fact r.Prime] (hA : A.LiesOverPrime r) {p : ℕ} (hp : p.Prime) (hpr : p ≠ r)
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : A.IsFrobeniusAt φ r)
    {x : AlgebraicClosure ℚ} (hx : x ^ p = 1) : φ x = x ^ r := by
  have hxA : x ∈ A := mem_of_pow_eq_one hp.ne_zero hx
  set a : ↥A := ⟨x, hxA⟩ with ha
  have hap : a ^ p = 1 := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hx)
  set φD : ↥(A.decompositionSubgroup ℚ) := ⟨φ, hφ.mem_decompositionSubgroup⟩ with hφD

  have h1 : ((φD • a : ↥A) : AlgebraicClosure ℚ) = φ x := rfl
  have h2 : (φD • a) ^ p = 1 := by rw [← smul_pow', hap, smul_one]
  have h3 : (a ^ r) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hap, one_pow]
  have h4 : IsLocalRing.residue ↥A (φD • a) = IsLocalRing.residue ↥A (a ^ r) := by
    rw [IsLocalRing.ResidueField.residue_smul, hφ.smul_residue_eq, map_pow]
  have := eq_of_pow_eq_one_of_residue_eq hA hp hpr h2 h3 h4
  rw [← h1, this, SubmonoidClass.coe_pow]

theorem exists_isPrimitiveRoot {p : ℕ} (hp : p.Prime) : ∃ μ : AlgebraicClosure ℚ, IsPrimitiveRoot μ p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdeg : (Polynomial.cyclotomic p (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime hp]
    exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨μ, Polynomial.isRoot_cyclotomic_iff.1 hμ⟩

theorem exists_coe_eq_of_pow_eq_one {p : ℕ} (hp : p.Prime) {ζ : A.valuation.Completion} (hζ : ζ ^ p = 1) :
    ∃ x : AlgebraicClosure ℚ, x ^ p = 1 ∧ ι A x = ζ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨μ, hμ⟩ := exists_isPrimitiveRoot hp
  have hμ' : IsPrimitiveRoot (ι A μ) p := hμ.map_of_injective (ι_injective A)
  obtain ⟨i, -, hi⟩ := hμ'.eq_pow_of_pow_eq_one hζ
  refine ⟨μ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]
  · rw [map_pow, hi]

theorem smul_eq_pow_of_pow_eq_one {r : ℕ} [Fact r.Prime] (hA : A.LiesOverPrime r) {p : ℕ} (hp : p.Prime)
    (hpr : p ≠ r) {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : A.IsFrobeniusAt φ r)
    (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion)
    (hs : ∀ c, s c = (⟨φ, hφ.mem_decompositionSubgroup⟩ : ↥(A.decompositionSubgroup ℚ)) • c)
    {ζ : A.valuation.Completion} (hζ : ζ ^ p = 1) : s ζ = ζ ^ r := by
  obtain ⟨x, hx, rfl⟩ := exists_coe_eq_of_pow_eq_one hp hζ
  rw [hs, ι_apply, ValuationSubring.smul_completion_coe]
  show ι A (φ x) = (ι A x) ^ r
  rw [← map_pow]
  exact congrArg _ (frob_apply_eq_pow hA hp hpr hφ hx)

end Roots

section Torus

variable {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
  {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)

theorem mem_U_of_smul_eq_zero {n : ℤ} (hn : n ≠ 0) {w : P.TorusPoints} (hw : n • w = 0) : w ∈ P.U := by
  change P.periodLattice.mkQ w ∈ Submodule.torsion ℤ P.JacPoints
  rw [Submodule.mem_torsion_iff]
  exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, by
    change n • P.periodLattice.mkQ w = 0
    rw [← map_zsmul, hw, map_zero]⟩

theorem smul_precomp_eq_zero (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) {n : ℤ} {w : P.TorusPoints}
    (hw : n • w = 0) : n • P.precomp f w = 0 := by
  rw [← map_zsmul, hw, map_zero]

theorem coeffMap_eq_smul_of_forall_eq_pow (s : L →+* L) {ζ : Lˣ} {r : ℕ} (hs : s ζ = ζ ^ r) (v : P.TorusPoints)
    (k : ↥(ribbonKernel D) → ℕ) (hv : ∀ z, Additive.toMul (v z) = ζ ^ k z) :
    P.coeffMap s v = (r : ℤ) • v := by
  apply LinearMap.ext
  intro z
  have hvz : v z = Additive.ofMul (ζ ^ k z) := by rw [← hv z, ofMul_toMul]
  rw [PeriodDatum.coeffMap_apply, LinearMap.smul_apply, hvz, toMul_ofMul]
  have : Units.map (s : L →* L) (ζ ^ k z) = (ζ ^ k z) ^ r := by
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      MonoidHom.coe_coe, map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]
  rw [this, ofMul_pow, natCast_zsmul]

theorem precomp_coeffMap_eq_smul (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) (s : L →+* L) {ζ : Lˣ} {r : ℕ}
    (hs : s ζ = ζ ^ r) (v : P.TorusPoints) (k : ↥(ribbonKernel D) → ℕ) (hv : ∀ z, Additive.toMul (v z) = ζ ^ k z) :
    P.precomp f (P.coeffMap s v) = (r : ℤ) • P.precomp f v := by
  rw [coeffMap_eq_smul_of_forall_eq_pow P s hs v k hv, map_zsmul]

theorem coeffMap_QL_eq (s : L →+* L) (x : ↥(ribbonKernel D))
    (h : ∀ y, s (algebraMap K L ((Additive.toMul (P.Q x y) : Kˣ) : K)) = algebraMap K L ((Additive.toMul (P.Q x y) : Kˣ) : K)) :
    P.coeffMap s (P.QL x) = P.QL x := by
  apply LinearMap.ext
  intro y
  rw [PeriodDatum.coeffMap_apply, PeriodDatum.QL_apply, ← ofMul_toMul ((P.Q x) y), unitsBaseChange_apply,
    toMul_ofMul]
  congr 1
  ext
  rw [Units.coe_map, MonoidHom.coe_coe, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact h y

theorem smul_coeffMap_sub_eq_zero (s : L →+* L) {n : ℤ} (u : P.TorusPoints) (x : ↥(ribbonKernel D))
    (hux : n • u = P.QL x) (hfix : P.coeffMap s (P.QL x) = P.QL x) : n • (P.coeffMap s u - u) = 0 := by
  rw [smul_sub, ← map_zsmul, hux, hfix, sub_self]

theorem precomp_coeffMap_eq_add (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) (s : L →+* L) (u : P.TorusPoints) :
    P.precomp f (P.coeffMap s u) = P.precomp f u + P.precomp f (P.coeffMap s u - u) := by
  rw [map_sub, add_sub_cancel]

theorem Umk_smul_eq_zero {n : ℤ} {a : P.TorusPoints} (ha : a ∈ P.U) (h : n • a = 0) : n • (⟨a, ha⟩ : ↥P.U) = 0 :=
  Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_zero]; exact h)

theorem Umk_mem_torsionBy {n : ℤ} {a : P.TorusPoints} (ha : a ∈ P.U) (h : n • a = 0) :
    (⟨a, ha⟩ : ↥P.U) ∈ Submodule.torsionBy ℤ (↥P.U) n :=
  (Submodule.mem_torsionBy_iff _ _).2 (Umk_smul_eq_zero P ha h)

theorem Umk_add {a b : P.TorusPoints} (ha : a ∈ P.U) (hb : b ∈ P.U) :
    (⟨a + b, P.U.add_mem ha hb⟩ : ↥P.U) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl

theorem Umk_congr {a b : P.TorusPoints} (hab : a = b) (ha : a ∈ P.U) (hb : b ∈ P.U) :
    (⟨a, ha⟩ : ↥P.U) = ⟨b, hb⟩ := Subtype.ext hab

theorem coe_smul_eq_zero_of_mem_torsionBy {n : ℤ} (v : ↥(Submodule.torsionBy ℤ (↥P.U) n)) :
    n • ((v : ↥P.U) : P.TorusPoints) = 0 := by
  have h := (Submodule.mem_torsionBy_iff n (v : ↥P.U)).1 v.2
  rw [← Submodule.coe_smul, h, Submodule.coe_zero]

theorem toMul_smul_precomp_apply (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) (n : ℕ) (v : P.TorusPoints)
    (ζ : Lˣ) (k : ↥(ribbonKernel D) → ℕ) (hv : ∀ z, Additive.toMul (v z) = ζ ^ k z) (z : ↥(ribbonKernel D)) :
    Additive.toMul (((n : ℤ) • P.precomp f v) z) = ζ ^ (k (f z) * n) := by
  rw [LinearMap.smul_apply, PeriodDatum.precomp_apply, toMul_zsmul, hv, zpow_natCast, ← pow_mul]

end Torus

theorem natCast_smul_comp_apply {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V} {p : ℕ}
    (g : ↥(ribbonKernel D) →ₗ[ℤ] ZMod p) (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) (n : ℕ)
    (z : ↥(ribbonKernel D)) : ((n : ℤ) • (g ∘ₗ f)) z = (n : ZMod p) * g (f z) := by
  rw [LinearMap.smul_apply, LinearMap.comp_apply, zsmul_eq_mul, Int.cast_natCast]

theorem zmod_eq_of_pow_eq {L : Type} [CommMonoid L] {p : ℕ} [NeZero p] {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (a b : ZMod p) (n : ℕ) (h : ζ ^ (b.val * n) = ζ ^ a.val) : a = (n : ZMod p) * b := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have h1 : a.val < p := ZMod.val_lt _
  have h2 : b.val * n % p < p := Nat.mod_lt _ hp
  have hmod : ζ ^ (b.val * n) = ζ ^ (b.val * n % p) := by
    conv_lhs => rw [← Nat.mod_add_div (b.val * n) p]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have key : ζ ^ (b.val * n % p) = ζ ^ a.val := by rw [← hmod, h]
  have h3 := hζ.pow_inj h2 h1 key
  apply ZMod.val_injective p
  rw [← h3, ZMod.val_mul, ZMod.val_natCast]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_comm]

section Laws

variable {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
  {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {D : DegeneracyData E V} {H : HeckeData D}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
  {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
  {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}

set_option maxHeartbeats 1600000 in
theorem frob_toric (hpr : p ≠ r) (𝒰 : PeriodUniformization r D H A hA T hecke gal)
    (ζ : (A.valuation.Completion)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (χ : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p))
    (hχ : ∀ (v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
      Additive.toMul ((((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) z)) = ζ ^ (χ v z).val)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ r)
    (v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ))) :
    ∃ v' : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)),
      gal φ (𝒰.e (v : ↥𝒰.P.U)) = 𝒰.e (v' : ↥𝒰.P.U) ∧
        χ v' = (r : ℤ) • ((χ v) ∘ₗ heckeKernelMap H ⟨r, Fact.out⟩) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hp.ne_zero
  obtain ⟨s, hs⟩ := exists_algEquiv_eq_smul A ⟨φ, hφ.mem_decompositionSubgroup⟩
  have hζp : (ζ : A.valuation.Completion) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  have hsζ : (s : A.valuation.Completion →+* A.valuation.Completion) ζ = ζ ^ r :=
    smul_eq_pow_of_pow_eq_one hA hp hpr hφ s hs hζp
  have hpv := coe_smul_eq_zero_of_mem_torsionBy 𝒰.P v

  have himg := precomp_coeffMap_eq_smul 𝒰.P (heckeKernelMap H ⟨r, Fact.out⟩) _ hsζ
    ((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) (fun z => (χ v z).val) (hχ v)
  have hpw : (p : ℤ) • ((r : ℤ) • 𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩)
      ((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints)) = 0 := by
    rw [smul_comm, smul_precomp_eq_zero 𝒰.P _ hpv, smul_zero]
  have hwU : (r : ℤ) • 𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) ((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) ∈ 𝒰.P.U :=
    mem_U_of_smul_eq_zero 𝒰.P hp0 hpw
  have hwU' : 𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩)
      (𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
        ((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints)) ∈ 𝒰.P.U := by
    rw [himg]; exact hwU
  have hwtor := Umk_mem_torsionBy 𝒰.P hwU hpw
  refine ⟨⟨⟨_, hwU⟩, hwtor⟩, ?_, ?_⟩
  · have h := 𝒰.e_frob ⟨φ, hφ.mem_decompositionSubgroup⟩ hφ s hs (v : ↥𝒰.P.U) hwU'
    rw [Umk_congr 𝒰.P himg hwU' hwU] at h
    exact h.symm
  · apply LinearMap.ext
    intro z
    have hlhs := hχ ⟨⟨_, hwU⟩, hwtor⟩ z
    have hval := toMul_smul_precomp_apply 𝒰.P (heckeKernelMap H ⟨r, Fact.out⟩) r
      ((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) ζ (fun z => (χ v z).val) (hχ v) z
    have key : ζ ^ ((χ v (heckeKernelMap H ⟨r, Fact.out⟩ z)).val * r) = ζ ^ (χ ⟨⟨_, hwU⟩, hwtor⟩ z).val :=
      hval.symm.trans hlhs
    refine Eq.trans ?_ (natCast_smul_comp_apply (χ v) (heckeKernelMap H ⟨r, Fact.out⟩) r z).symm
    exact zmod_eq_of_pow_eq hζ _ _ r key

set_option maxHeartbeats 1600000 in
theorem frob_quot (𝒰 : PeriodUniformization r D H A hA T hecke gal)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ r)
    (u : ↥𝒰.P.U) (x : ↥(ribbonKernel D)) (hux : (p : ℤ) • (u : 𝒰.P.TorusPoints) = 𝒰.P.QL x)
    (hu : 𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : 𝒰.P.TorusPoints) ∈ 𝒰.P.U) :
    ∃ v : ↥𝒰.P.U, (p : ℤ) • v = 0 ∧
      gal φ (𝒰.e u) = 𝒰.e ⟨𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : 𝒰.P.TorusPoints), hu⟩ + 𝒰.e v := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hp.ne_zero
  obtain ⟨s, hs⟩ := exists_algEquiv_eq_smul A ⟨φ, hφ.mem_decompositionSubgroup⟩
  have hfix := coeffMap_QL_eq 𝒰.P (s : A.valuation.Completion →+* A.valuation.Completion) x
    (fun y => 𝒰.decomp_Q ⟨φ, hφ.mem_decompositionSubgroup⟩ s hs x y)
  have hpw := smul_coeffMap_sub_eq_zero 𝒰.P (s : A.valuation.Completion →+* A.valuation.Completion)
    (u : 𝒰.P.TorusPoints) x hux hfix
  have hpKw := smul_precomp_eq_zero 𝒰.P (heckeKernelMap H ⟨r, Fact.out⟩) hpw
  have hKwU := mem_U_of_smul_eq_zero 𝒰.P hp0 hpKw
  have hsum := precomp_coeffMap_eq_add 𝒰.P (heckeKernelMap H ⟨r, Fact.out⟩)
    (s : A.valuation.Completion →+* A.valuation.Completion) (u : 𝒰.P.TorusPoints)
  have hu' : 𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩)
      (𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : 𝒰.P.TorusPoints)) ∈ 𝒰.P.U := by
    rw [hsum]
    exact 𝒰.P.U.add_mem hu hKwU
  refine ⟨⟨_, hKwU⟩, Umk_smul_eq_zero 𝒰.P hKwU hpKw, ?_⟩
  have hfrob := 𝒰.e_frob ⟨φ, hφ.mem_decompositionSubgroup⟩ hφ s hs u hu'
  rw [← hfrob, Umk_congr 𝒰.P hsum hu' (𝒰.P.U.add_mem hu hKwU), Umk_add 𝒰.P hu hKwU, map_add]

end Laws

end CerednikDrinfeld.Mumford.FrobLaws
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld.Mumford.FrobLaws"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld.Mumford"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.CerednikDrinfeld.Mumford.FrobLaws"

open CerednikDrinfeld.Mumford.FrobLaws in
theorem solution
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} {H : HeckeData D}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
    {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
    (𝒰 : PeriodUniformization r D H A hA T hecke gal)
    (ζ : (A.valuation.Completion)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (χ : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p))
    (hχ : ∀ (v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
      Additive.toMul ((((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) z)) = ζ ^ (χ v z).val) :
    (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)), ∃ v' : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)),
        gal φ (𝒰.e (v : ↥𝒰.P.U)) = 𝒰.e (v' : ↥𝒰.P.U) ∧
          χ v' = (r : ℤ) • ((χ v) ∘ₗ heckeKernelMap H ⟨r, Fact.out⟩)) ∧
    (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ (u : ↥𝒰.P.U) (x : ↥(ribbonKernel D)), (p : ℤ) • (u : 𝒰.P.TorusPoints) = 𝒰.P.QL x →
        ∀ hu : 𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : 𝒰.P.TorusPoints) ∈ 𝒰.P.U,
          ∃ v : ↥𝒰.P.U, (p : ℤ) • v = 0 ∧
            gal φ (𝒰.e u) = 𝒰.e ⟨𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : 𝒰.P.TorusPoints), hu⟩ + 𝒰.e v) :=
  ⟨fun φ hφ v => frob_toric hpr 𝒰 ζ hζ χ hχ φ hφ v, fun φ hφ u x hux hu => frob_quot 𝒰 φ hφ u x hux hu⟩

end S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv (solution)
