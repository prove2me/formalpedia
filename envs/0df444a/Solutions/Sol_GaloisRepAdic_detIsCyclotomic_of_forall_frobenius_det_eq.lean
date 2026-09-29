-- Prove2me | solution 1 for GaloisRepAdic.detIsCyclotomic_of_forall_frobenius_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e6575342-6a84-5c48-b00f-a30ecf1668e4

import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_FrobeniusDensity_exists_frobenius_conj_pow_of_statement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Filtration
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_forall_quotient
import Theorems.Thm_GaloisRepAdic_det_baseChangeAlong
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

open Polynomial Module

namespace RT2DenAux4

lemma repr_mem_of_mem_ideal_smul_top {A : Type} [CommRing A] {V : Type} [AddCommGroup V]
    [Module A V] {ι : Type} (b : Basis ι A V) (I : Ideal A) {x : V}
    (hx : x ∈ I • (⊤ : Submodule A V)) (i : ι) : b.repr x i ∈ I := by
  rw [← b.span_eq] at hx
  obtain ⟨a, haI, rfl⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I (⇑b) _).mp hx
  have h : (a.sum fun i c => c • b i) = b.repr.symm a := by
    rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  rw [h, LinearEquiv.apply_symm_apply]
  exact haI i

lemma toMatrix_map_quotient_eq_one {A : Type} [CommRing A] {V : Type} [AddCommGroup V]
    [Module A V] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι A V) (I : Ideal A)
    {f : Module.End A V} (hf : ∀ v : V, f v - v ∈ I • (⊤ : Submodule A V)) :
    (LinearMap.toMatrix b b f).map (Ideal.Quotient.mk I) = 1 := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply]
  have hmem : b.repr (f (b j)) i - b.repr (b j) i ∈ I := by
    have h : b.repr (f (b j)) i - b.repr (b j) i = b.repr (f (b j) - b j) i := by
      rw [map_sub, Finsupp.sub_apply]
    rw [h]
    exact repr_mem_of_mem_ideal_smul_top b I (hf (b j)) i
  have hq : Ideal.Quotient.mk I (b.repr (f (b j)) i) = Ideal.Quotient.mk I (b.repr (b j) i) :=
    Ideal.Quotient.eq.mpr hmem
  rw [hq, Basis.repr_self_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

lemma charpoly_mul_map_quotient_eq {A : Type} [CommRing A] {V : Type} [AddCommGroup V]
    [Module A V] [Module.Free A V] [Module.Finite A V] (I : Ideal A) (f g : Module.End A V)
    (hg : ∀ v : V, g v - v ∈ I • (⊤ : Submodule A V)) :
    (LinearMap.charpoly (f * g)).map (Ideal.Quotient.mk I) =
      (LinearMap.charpoly f).map (Ideal.Quotient.mk I) := by
  classical
  let b := Module.Free.chooseBasis A V
  rw [← LinearMap.charpoly_toMatrix (f * g) b, ← LinearMap.charpoly_toMatrix f b,
    ← Matrix.charpoly_map _ (Ideal.Quotient.mk I), ← Matrix.charpoly_map _ (Ideal.Quotient.mk I),
    LinearMap.toMatrix_mul b, Matrix.map_mul, toMatrix_map_quotient_eq_one b I hg, mul_one]

private lemma _root_.RT2DenAux4.charpoly_conj {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
    [Module.Free A V] [Module.Finite A V] {G : Type} [Group G] (ρ : G →* Module.End A V)
    (γ x : G) : LinearMap.charpoly (ρ (γ * x * γ⁻¹)) = LinearMap.charpoly (ρ x) := by
  have h₁ : (ρ γ).comp (ρ γ⁻¹) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h₂ : (ρ γ⁻¹).comp (ρ γ) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl
  have he : ρ (γ * x * γ⁻¹) = (LinearEquiv.ofLinear (ρ γ) (ρ γ⁻¹) h₁ h₂).conj (ρ x) := by
    apply LinearMap.ext; intro v
    simp only [map_mul, Module.End.mul_apply, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, LinearEquiv.ofLinear_symm_apply]
  rw [he, LinearEquiv.charpoly_conj]

p2m_export "RT2DenAux4" "charpoly_conj"

lemma charpoly_map_quotient_eq_pow_of_fixes {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (I : Ideal A) {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hL : ∀ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ' x = x) →
      ∀ v : ρ.V, ρ.ρ σ' v - v ∈ I • (⊤ : Submodule A ρ.V))
    {σ τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {j : ℕ}
    (hfix : ∀ x ∈ L, σ x = (γ * τ ^ j * γ⁻¹) x) :
    (LinearMap.charpoly (ρ.ρ σ)).map (Ideal.Quotient.mk I) =
      (LinearMap.charpoly ((ρ.ρ τ) ^ j)).map (Ideal.Quotient.mk I) := by
  set c := γ * τ ^ j * γ⁻¹ with hc
  have hσ : σ = c * (c⁻¹ * σ) := by rw [mul_inv_cancel_left]
  have hfixc : ∀ x ∈ L, (c⁻¹ * σ) x = x := by
    intro x hx
    rw [AlgEquiv.mul_apply, hfix x hx, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hmain := charpoly_mul_map_quotient_eq I (ρ.ρ c) (ρ.ρ (c⁻¹ * σ)) (hL _ hfixc)
  rw [← map_mul, ← hσ] at hmain
  rw [hmain, hc, charpoly_conj ρ.ρ γ (τ ^ j), map_pow]

lemma det_map_quotient_eq_pow_of_fixes {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (I : Ideal A) {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hL : ∀ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ' x = x) →
      ∀ v : ρ.V, ρ.ρ σ' v - v ∈ I • (⊤ : Submodule A ρ.V))
    {σ τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {j : ℕ}
    (hfix : ∀ x ∈ L, σ x = (γ * τ ^ j * γ⁻¹) x) :
    Ideal.Quotient.mk I (LinearMap.det (ρ.ρ σ)) =
      Ideal.Quotient.mk I (LinearMap.det (ρ.ρ τ) ^ j) := by
  have h := charpoly_map_quotient_eq_pow_of_fixes ρ I hL hfix
  have h0 : Ideal.Quotient.mk I ((LinearMap.charpoly (ρ.ρ σ)).coeff 0) =
      Ideal.Quotient.mk I ((LinearMap.charpoly ((ρ.ρ τ) ^ j)).coeff 0) := by
    have hc := congrArg (fun P => P.coeff 0) h
    simpa [Polynomial.coeff_map] using hc
  have hd1 : LinearMap.det (ρ.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).coeff 0 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, ρ.finrank_eq, neg_one_sq, one_mul]
  have hd2 : LinearMap.det ((ρ.ρ τ) ^ j) = (LinearMap.charpoly ((ρ.ρ τ) ^ j)).coeff 0 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, ρ.finrank_eq, neg_one_sq, one_mul]
  calc Ideal.Quotient.mk I (LinearMap.det (ρ.ρ σ))
      = Ideal.Quotient.mk I ((LinearMap.charpoly (ρ.ρ σ)).coeff 0) := by rw [hd1]
    _ = Ideal.Quotient.mk I ((LinearMap.charpoly ((ρ.ρ τ) ^ j)).coeff 0) := h0
    _ = Ideal.Quotient.mk I (LinearMap.det ((ρ.ρ τ) ^ j)) := by rw [hd2]
    _ = Ideal.Quotient.mk I (LinearMap.det (ρ.ρ τ) ^ j) := by rw [map_pow]

end RT2DenAux4

p2m_open "IsLocalRing Module.IsLocalRing"

namespace RT2Density

section Place

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem vs_mul_mem_nonunits {a x : L} (ha : a ∈ A) (hx : x ∈ A.nonunits) :
    a * x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

theorem vs_one_notMem_nonunits : (1 : L) ∉ A.nonunits := by
  simp [ValuationSubring.mem_nonunits_iff]

theorem vs_pow_mem_nonunits {x : L} (hx : x ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) :
    x ^ n ∈ A.nonunits := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact vs_mul_mem_nonunits (pow_mem (A.nonunits_subset hx) m) hx

theorem vs_mem_of_pow_eq_one {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : ζ ∈ A := by
  by_contra hmem
  have h2 : (ζ⁻¹) ^ n ∈ A.nonunits :=
    vs_pow_mem_nonunits (A.inv_mem_nonunits_iff.mpr (Or.inr hmem)) hn
  rw [inv_pow, hζ, inv_one] at h2
  exact vs_one_notMem_nonunits h2

theorem vs_notMem_nonunits_of_pow_eq_one {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    ζ ∉ A.nonunits := fun h1 => vs_one_notMem_nonunits (A := A) (hζ ▸ vs_pow_mem_nonunits h1 hn)

theorem vs_eq_one_of_pow_eq_one_of_sub_one_mem_nonunits {m : ℕ}
    (hm : (m : ResidueField A) ≠ 0) {ω : L} (hω : ω ^ m = 1) (h1 : ω - 1 ∈ A.nonunits) :
    ω = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  by_contra hne
  have hωA : ω ∈ A := vs_mem_of_pow_eq_one hm0 hω
  have hres : residue A (⟨ω, hωA⟩ : A) = 1 := by
    have hmem : (⟨ω, hωA⟩ : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
      rw [← A.coe_mem_nonunits_iff]
      simpa using h1
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_sub, map_one, sub_eq_zero] at h0
  have hgeom : (∑ i ∈ Finset.range m, (⟨ω, hωA⟩ : A) ^ i) = 0 := by
    have hL : (∑ i ∈ Finset.range m, ω ^ i) * (ω - 1) = 0 := by
      rw [geom_sum_mul, hω, sub_self]
    have hsum : (∑ i ∈ Finset.range m, ω ^ i) = 0 :=
      (mul_eq_zero.mp hL).resolve_right (sub_ne_zero.mpr hne)
    exact Subtype.ext (by push_cast; exact hsum)
  refine hm ?_
  have h0 := congrArg (residue A) hgeom
  rw [map_sum, map_zero] at h0
  simp only [map_pow, hres, one_pow] at h0
  simpa using h0

theorem vs_natCast_mem_maximalIdeal_of_liesOverPrime {q : ℕ} (h : A.LiesOverPrime q) :
    (q : A) ∈ IsLocalRing.maximalIdeal A := by
  have : ((q : A) : L) ∈ A.nonunits := by simp at h ⊢; exact h
  exact A.coe_mem_nonunits_iff.mp this

theorem vs_charP_residueField_of_liesOverPrime {q : ℕ} (hq : q.Prime)
    (h : A.LiesOverPrime q) : CharP (IsLocalRing.ResidueField A) q := by
  rw [CharP.charP_iff_prime_eq_zero hq]
  have : ((q : ℕ) : IsLocalRing.ResidueField A) = IsLocalRing.residue A ((q : ℕ) : A) := by
    simp
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (vs_natCast_mem_maximalIdeal_of_liesOverPrime h)

theorem vs_natCast_residueField_ne_zero_of_not_dvd {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {m : ℕ} (hqm : ¬q ∣ m) : (m : ResidueField A) ≠ 0 := by
  haveI : CharP (ResidueField A) q := vs_charP_residueField_of_liesOverPrime hq hA
  rw [Ne, CharP.cast_eq_zero_iff (ResidueField A) q]
  exact hqm

variable {K : Type*} [Field K] [Algebra K L]

open scoped Pointwise in
theorem vs_smul_mem_of_mem_decompositionSubgroup {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {z : L} (hz : z ∈ A) : σ z ∈ A := by
  have h1 : σ • z ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ z A hz
  rwa [MulAction.mem_stabilizer_iff.mp hσ, AlgEquiv.smul_def] at h1

theorem frob_residue_smul_eq {σ : L ≃ₐ[K] L} {q : ℕ} (h : A.IsFrobeniusAt σ q) (a : A) :
    residue A ((⟨σ, h.mem_decompositionSubgroup⟩ : A.decompositionSubgroup K) • a) =
      (residue A a) ^ q := by
  rw [ResidueField.residue_smul]
  exact h.smul_residue_eq (residue A a)

theorem frob_apply_eq_pow_of_pow_eq_one {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) {m : ℕ} (hm : (m : ResidueField A) ≠ 0) {ζ : L}
    (hζ : ζ ^ m = 1) : σ ζ = ζ ^ q := by
  have hσd := h.mem_decompositionSubgroup
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hζ
    exact zero_ne_one hζ
  have hζA : ζ ∈ A := vs_mem_of_pow_eq_one hm0 hζ
  have hζnu : ζ ∉ A.nonunits := vs_notMem_nonunits_of_pow_eq_one hm0 hζ
  have hζinv : ζ⁻¹ ∈ A := by
    have h' := hζnu
    rw [ValuationSubring.mem_nonunits_iff_or] at h'
    exact not_not.mp (not_or.mp h').2
  have hσζA : σ ζ ∈ A := vs_smul_mem_of_mem_decompositionSubgroup hσd hζA
  have hres : residue A (⟨σ ζ, hσζA⟩ : A) = (residue A (⟨ζ, hζA⟩ : A)) ^ q := by
    have h1 : residue A (⟨σ ζ, hσζA⟩ : A)
        = residue A ((⟨σ, hσd⟩ : A.decompositionSubgroup K) • (⟨ζ, hζA⟩ : A)) := rfl
    rw [h1, frob_residue_smul_eq h]
  have hsub : σ ζ - ζ ^ q ∈ A.nonunits := by
    have h0 : residue A ((⟨σ ζ, hσζA⟩ : A) - (⟨ζ, hζA⟩ : A) ^ q) = 0 := by
      rw [map_sub, map_pow, hres, sub_self]
    have hmem : (⟨σ ζ, hσζA⟩ : A) - (⟨ζ, hζA⟩ : A) ^ q ∈ IsLocalRing.maximalIdeal A :=
      Ideal.Quotient.eq_zero_iff_mem.mp h0
    simpa using A.coe_mem_nonunits_iff.mpr hmem
  have hωm : (σ ζ * (ζ⁻¹) ^ q) ^ m = 1 := by
    have h1 : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have h2 : ((ζ⁻¹) ^ q) ^ m = 1 := by
      rw [← pow_mul, mul_comm q m, pow_mul, inv_pow, hζ, inv_one, one_pow]
    rw [mul_pow, h1, h2, one_mul]
  have hω1 : σ ζ * (ζ⁻¹) ^ q - 1 ∈ A.nonunits := by
    have hinvpow : (ζ⁻¹) ^ q * ζ ^ q = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hζ0, one_pow]
    have heq : σ ζ * (ζ⁻¹) ^ q - 1 = (ζ⁻¹) ^ q * (σ ζ - ζ ^ q) := by
      rw [mul_sub, hinvpow, mul_comm ((ζ⁻¹) ^ q) (σ ζ)]
    rw [heq]
    exact vs_mul_mem_nonunits (pow_mem hζinv q) hsub
  have hone : σ ζ * (ζ⁻¹) ^ q = 1 :=
    vs_eq_one_of_pow_eq_one_of_sub_one_mem_nonunits hm hωm hω1
  have hζq0 : ζ ^ q ≠ 0 := pow_ne_zero q hζ0
  rw [inv_pow, mul_inv_eq_one₀ hζq0] at hone
  exact hone

theorem frob_apply_eq_pow_of_pow_prime_pow_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : A.IsFrobeniusAt σ q)
    (n : ℕ) {ζ : L} (hζ : ζ ^ p ^ n = 1) : σ ζ = ζ ^ q := by
  refine frob_apply_eq_pow_of_pow_eq_one hσ ?_ hζ
  refine vs_natCast_residueField_ne_zero_of_not_dvd hq hA fun hdvd => hqp ?_
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)

theorem frob_pow_apply_eq_pow_of_pow_prime_pow_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : A.IsFrobeniusAt σ q)
    (n : ℕ) {ζ : L} (hζ : ζ ^ p ^ n = 1) (j : ℕ) : (σ ^ j) ζ = ζ ^ q ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, AlgEquiv.mul_apply, frob_apply_eq_pow_of_pow_prime_pow_eq_one hp hq hqp hA hσ
      n hζ, map_pow, ih, ← pow_mul, ← pow_succ]

end Place

section Cyclotomic

theorem exists_isPrimitiveRoot_prime_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (p ^ n) := by
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := ⟨by exact_mod_cast hp.ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)

theorem finiteDimensional_sup_adjoin (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L₀] (ζ : AlgebraicClosure ℚ) :
    FiniteDimensional ℚ (L₀ ⊔ IntermediateField.adjoin ℚ {ζ} :
      IntermediateField ℚ (AlgebraicClosure ℚ)) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) ζ).isIntegral
  infer_instance

theorem mem_sup_adjoin_self (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ) :
    ζ ∈ (L₀ ⊔ IntermediateField.adjoin ℚ {ζ} : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
  (le_sup_right : IntermediateField.adjoin ℚ {ζ} ≤ L₀ ⊔ IntermediateField.adjoin ℚ {ζ})
    (IntermediateField.mem_adjoin_simple_self ℚ ζ)

theorem mem_sup_adjoin_of_mem (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ) {x : AlgebraicClosure ℚ} (hx : x ∈ L₀) :
    x ∈ (L₀ ⊔ IntermediateField.adjoin ℚ {ζ} : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
  (le_sup_left : L₀ ≤ L₀ ⊔ IntermediateField.adjoin ℚ {ζ}) hx

theorem pow_modEq_of_frobenius_conj {p : ℕ} (hp : p.Prime) (n : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓp : ℓ ≠ p) {B : ValuationSubring (AlgebraicClosure ℚ)} (hB : B.LiesOverPrime ℓ)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : B.IsFrobeniusAt τ ℓ)
    (γ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (j a : ℕ)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (hσζ : σ ζ = (γ * τ ^ j * γ⁻¹) ζ)
    (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) :
    ℓ ^ j ≡ a [MOD p ^ n] := by
  have hζ' : (γ⁻¹ ζ) ^ p ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h1 : (γ * τ ^ j * γ⁻¹) ζ = ζ ^ ℓ ^ j := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply,
      frob_pow_apply_eq_pow_of_pow_prime_pow_eq_one hp hℓ hℓp hB hτ n hζ' j, map_pow,
      ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have h2 : ζ ^ ℓ ^ j = ζ ^ a := by rw [← h1, ← hσζ, ha ζ hζ.pow_eq_one]
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  rw [pow_eq_pow_mod (ℓ ^ j) hζ.pow_eq_one, pow_eq_pow_mod a hζ.pow_eq_one] at h2
  exact hζ.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h2

theorem natCast_sub_natCast_mem_span_of_modEq {R : Type*} [CommRing R] {k x y : ℕ}
    (h : x ≡ y [MOD k]) : (x : R) - (y : R) ∈ Ideal.span {((k : ℕ) : R)} := by
  rw [Ideal.mem_span_singleton]
  have hz : (k : ℤ) ∣ (x : ℤ) - (y : ℤ) := (Nat.modEq_iff_dvd.mp h.symm)
  obtain ⟨c, hc⟩ := hz
  refine ⟨(c : R), ?_⟩
  have := congrArg (Int.cast : ℤ → R) hc
  push_cast at this
  exact this

end Cyclotomic

end RT2Density

open RT2DenAux4 RT2Density in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) (S : Finset ℕ)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        LinearMap.det (ρ.ρ τ) = (ℓ : A)) :
    ρ.DetIsCyclotomic p := by
  refine GaloisRepAdic.detIsCyclotomic_of_forall_quotient ρ fun m => ?_
  set I : Ideal A := IsLocalRing.maximalIdeal A ^ (m + 1) with hI
  haveI hnt : Nontrivial (A ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
      (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
  haveI hloc : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hφ : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_⟩
  ·
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hpA ⊢
    intro hu
    apply hpA
    rw [← map_natCast (Ideal.Quotient.mk I)] at hu
    exact (isUnit_map_iff (Ideal.Quotient.mk I) (p : A)).mp hu
  · intro n σ a ha

    have hdetbc : LinearMap.det ((ρ.baseChangeAlong (Ideal.Quotient.mk I) hφ).ρ σ) =
        Ideal.Quotient.mk I (LinearMap.det (ρ.ρ σ)) :=
      GaloisRepAdic.det_baseChangeAlong (Ideal.Quotient.mk I) hφ ρ σ
    rw [hdetbc]

    obtain ⟨L₀, hfd₀, hL₀⟩ := ρ.isAdicContinuous (m + 1)
    haveI := hfd₀
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_prime_pow hp n
    haveI := finiteDimensional_sup_adjoin L₀ ζ
    obtain ⟨ℓ, hℓ, hℓS, B, τ, γ, j, hBℓ, hτ, hfix⟩ :=
      FrobeniusDensity.exists_frobenius_conj_pow_of_statement
        (fun M hF hN hG => @FrobeniusDensity.statement M hF hN hG)
        (L₀ ⊔ IntermediateField.adjoin ℚ {ζ}) σ (S ∪ {p})
    have hℓS' : ℓ ∉ S := fun h => hℓS (Finset.mem_union_left _ h)
    have hℓp : ℓ ≠ p := fun h => hℓS (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))

    have hL : ∀ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ (L₀ ⊔ IntermediateField.adjoin ℚ {ζ} : IntermediateField ℚ (AlgebraicClosure ℚ)),
          σ' x = x) → ∀ v : ρ.V, ρ.ρ σ' v - v ∈ I • (⊤ : Submodule A ρ.V) :=
      fun σ' hσ' => hL₀ σ' fun x hx => hσ' x (mem_sup_adjoin_of_mem L₀ ζ hx)
    have hrep : Ideal.Quotient.mk I (LinearMap.det (ρ.ρ σ)) = ((ℓ : A ⧸ I)) ^ j := by
      rw [det_map_quotient_eq_pow_of_fixes ρ I hL hfix, hdet ℓ hℓ hℓS' B τ hBℓ hτ, map_pow,
        map_natCast]

    have hcyc : ℓ ^ j ≡ a [MOD p ^ n] :=
      pow_modEq_of_frobenius_conj hp n hℓ hℓp hBℓ hτ γ σ j a hζ
        (hfix ζ (mem_sup_adjoin_self L₀ ζ)) ha
    have hspan := natCast_sub_natCast_mem_span_of_modEq (R := A ⧸ I) hcyc
    rw [hrep, ← Nat.cast_pow]
    exact hspan

end S_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq
end P2MW
export P2MW.S_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq (solution)
