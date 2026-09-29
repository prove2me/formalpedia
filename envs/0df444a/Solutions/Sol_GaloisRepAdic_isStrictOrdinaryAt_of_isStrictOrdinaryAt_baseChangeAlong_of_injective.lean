-- Prove2me | solution 1 for GaloisRepAdic.isStrictOrdinaryAt_of_isStrictOrdinaryAt_baseChangeAlong_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1e3ecfac-7632-5335-b34f-032c7200c6df

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_isStrictOrdinaryAt_baseChangeAlong_of_injective

set_option autoImplicit false

open scoped TensorProduct

namespace DescStrAsm

open IsLocalRing

section Coord

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
  (b : Module.Basis (Fin 2) A V)

theorem repr_one_eq_zero_of_mem {v : V} (hv : v ∈ A ∙ b 0) : b.repr v 1 = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, if_neg (by decide),
    smul_zero]

theorem mem_of_repr_one_eq_zero {v : V} (hv : b.repr v 1 = 0) : v ∈ A ∙ b 0 := by
  have h := b.sum_repr v
  rw [Fin.sum_univ_two, hv, zero_smul, add_zero] at h
  rw [← h]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem mem_iff_repr_one_eq_zero (v : V) : v ∈ A ∙ b 0 ↔ b.repr v 1 = 0 :=
  ⟨repr_one_eq_zero_of_mem b, mem_of_repr_one_eq_zero b⟩

noncomputable def xc (f : V →ₗ[A] V) : A := b.repr (f (b 0)) 0

noncomputable def yc (f : V →ₗ[A] V) : A := b.repr (f (b 1)) 0

noncomputable def zc (f : V →ₗ[A] V) : A := b.repr (f (b 1)) 1

def Pres (f : V →ₗ[A] V) : Prop := ∀ v ∈ A ∙ b 0, f v ∈ A ∙ b 0

variable {b}

theorem apply_b0 {f : V →ₗ[A] V} (hf : Pres b f) : f (b 0) = xc b f • b 0 := by
  have h := b.sum_repr (f (b 0))
  rw [Fin.sum_univ_two, repr_one_eq_zero_of_mem b (hf _ (Submodule.mem_span_singleton_self _)),
    zero_smul, add_zero] at h
  exact h.symm

theorem apply_b1 (f : V →ₗ[A] V) : f (b 1) = yc b f • b 0 + zc b f • b 1 := by
  have h := b.sum_repr (f (b 1))
  rw [Fin.sum_univ_two] at h
  exact h.symm

theorem repr_b0_one : b.repr (b 0) 1 = 0 := by
  rw [b.repr_self, Finsupp.single_apply, if_neg (by decide)]

theorem repr_b1_one : b.repr (b 1) 1 = 1 := by
  rw [b.repr_self, Finsupp.single_apply, if_pos rfl]

theorem apply_eq_xc_smul {f : V →ₗ[A] V} (hf : Pres b f) {w : V} (hw : w ∈ A ∙ b 0) :
    f w = xc b f • w := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, apply_b0 hf, smul_comm]

theorem sub_zc_smul_mem {f : V →ₗ[A] V} (hf : Pres b f) (v : V) :
    f v - zc b f • v ∈ A ∙ b 0 := by
  rw [mem_iff_repr_one_eq_zero]
  have h := b.sum_repr v
  rw [Fin.sum_univ_two] at h
  rw [← h]
  simp only [map_add, map_sub, map_smul, smul_add, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, smul_eq_mul, apply_b0 hf, apply_b1 f, repr_b0_one, repr_b1_one]
  ring

theorem eq_xc_of_apply_eq_smul {f : V →ₗ[A] V} {x : A}
    (hx : f (b 0) = x • b 0) : x = xc b f := by
  have h := congrArg (fun v => b.repr v 0) hx
  simp only [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] at h
  exact h.symm

theorem eq_zc_of_sub_smul_mem {f : V →ₗ[A] V} {z : A} (hz : f (b 1) - z • b 1 ∈ A ∙ b 0) :
    z = zc b f := by
  have h1 := repr_one_eq_zero_of_mem b hz
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_b1_one, smul_eq_mul,
    mul_one, sub_eq_zero] at h1
  exact h1.symm

theorem repr_mem_of_mem_smul_top {I : Ideal A} {v : V} (hv : v ∈ I • (⊤ : Submodule A V))
    (i : Fin 2) : b.repr v i ∈ I := by
  refine Submodule.smul_induction_on (p := fun v => b.repr v i ∈ I) hv ?_ ?_
  · intro a ha w _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · intro x y hx hy
    rw [map_add, Finsupp.add_apply]
    exact I.add_mem hx hy

theorem span_eq_span_of_mem [IsLocalRing A] {c : Module.Basis (Fin 2) A V} {w : V}
    (hw : w ∈ A ∙ c 0) (b' : Module.Basis (Fin 2) A V) (hb' : b' 0 = w) : A ∙ c 0 = A ∙ w := by
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hμ : IsUnit μ := by
    by_contra hμ
    have hmem : μ • c 0 ∈ (maximalIdeal A) • (⊤ : Submodule A V) :=
      Submodule.smul_mem_smul ((mem_maximalIdeal μ).mpr hμ) Submodule.mem_top
    have h1 := repr_mem_of_mem_smul_top (b := b') hmem 0
    rw [← hb', b'.repr_self, Finsupp.single_eq_same] at h1
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  exact (Submodule.span_singleton_smul_eq hμ (c 0)).symm

end Coord

section BasisExt

variable {A : Type} [CommRing A] [IsLocalRing A] {V : Type} [AddCommGroup V] [Module A V]

theorem exists_basis_of_notMem (e : Module.Basis (Fin 2) A V) (w : V)
    (hw : w ∉ (maximalIdeal A) • (⊤ : Submodule A V)) :
    ∃ b : Module.Basis (Fin 2) A V, b 0 = w := by
  classical
  have hsum : w = e.repr w 0 • e 0 + e.repr w 1 • e 1 := by
    have h := e.sum_repr w
    rw [Fin.sum_univ_two] at h
    exact h.symm

  have hunit : IsUnit (e.repr w 0) ∨ IsUnit (e.repr w 1) := by
    by_contra h
    push Not at h
    apply hw
    rw [hsum]
    exact Submodule.add_mem _
      (Submodule.smul_mem_smul ((mem_maximalIdeal _).mpr h.1) Submodule.mem_top)
      (Submodule.smul_mem_smul ((mem_maximalIdeal _).mpr h.2) Submodule.mem_top)
  rcases hunit with h0 | h1
  ·
    let f : V →ₗ[A] V := e.constr A ![w, e 1]
    have hf0 : f (e 0) = w := by
      show e.constr A ![w, e 1] (e 0) = w
      rw [Module.Basis.constr_basis]; rfl
    have hf1 : f (e 1) = e 1 := by
      show e.constr A ![w, e 1] (e 1) = e 1
      rw [Module.Basis.constr_basis]; rfl
    have hdet : IsUnit (LinearMap.toMatrix e e f).det := by
      rw [Matrix.det_fin_two]
      simp only [LinearMap.toMatrix_apply, hf0, hf1, e.repr_self, Finsupp.single_apply]
      simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte, mul_one, zero_mul, sub_zero]
      exact h0
    refine ⟨e.map (LinearEquiv.ofIsUnitDet hdet), ?_⟩
    rw [Module.Basis.map_apply, LinearEquiv.ofIsUnitDet_apply, hf0]
  ·
    let f : V →ₗ[A] V := e.constr A ![w, e 0]
    have hf0 : f (e 0) = w := by
      show e.constr A ![w, e 0] (e 0) = w
      rw [Module.Basis.constr_basis]; rfl
    have hf1 : f (e 1) = e 0 := by
      show e.constr A ![w, e 0] (e 1) = e 0
      rw [Module.Basis.constr_basis]; rfl
    have hdet : IsUnit (LinearMap.toMatrix e e f).det := by
      rw [Matrix.det_fin_two]
      simp only [LinearMap.toMatrix_apply, hf0, hf1, e.repr_self, Finsupp.single_apply]
      simp only [Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte, mul_zero, ↓reduceIte, one_mul,
        zero_sub, IsUnit.neg_iff]
      exact h1
    refine ⟨e.map (LinearEquiv.ofIsUnitDet hdet), ?_⟩
    rw [Module.Basis.map_apply, LinearEquiv.ofIsUnitDet_apply, hf0]

end BasisExt

section Cyclotomic

variable (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (p : ℕ) [hp : Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

scoped instance neZero_prime_rat : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩

noncomputable def eps (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : 𝒪 :=
  GaloisRep.padicIntToRing 𝒪 p hp𝒪
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) :
      ℤ_[p]ˣ) : ℤ_[p])

theorem exists_pow_eq_and_eps_sub_mem (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : ℕ) :
    ∃ b : ℕ, (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ m = 1 → σ μ = μ ^ b) ∧
      eps 𝒪 p hp𝒪 σ - (b : 𝒪) ∈ Ideal.span {((p ^ m : ℕ) : 𝒪)} := by
  set c : ℤ_[p] := ((cyclotomicCharacter (AlgebraicClosure ℚ) p
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : ℤ_[p]ˣ) : ℤ_[p]) with hc
  refine ⟨(PadicInt.toZModPow m c).val, ?_, ?_⟩
  · intro μ hμ
    have := cyclotomicCharacter.spec p (n := m) (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) μ hμ
    exact this
  · have hker : c - ((PadicInt.toZModPow m c).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
        sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hker
    rw [Ideal.mem_span_singleton']
    refine ⟨GaloisRep.padicIntToRing 𝒪 p hp𝒪 y, ?_⟩
    have := congrArg (GaloisRep.padicIntToRing 𝒪 p hp𝒪) hy
    rw [map_mul, map_pow, map_natCast, map_sub, map_natCast] at this
    rw [Nat.cast_pow]
    exact this

omit hp in

theorem natCast_sub_natCast_mem_of_pow_eq (R : Type) [CommRing R] [Fact p.Prime]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n a b : ℕ)
    (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a)
    (hb : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ b) :
    (a : R) - (b : R) ∈ Ideal.span {((p ^ n : ℕ) : R)} := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
  have h1 : ζ ^ a = ζ ^ b := by rw [← ha ζ hζ.pow_eq_one, hb ζ hζ.pow_eq_one]
  have hk : p ^ n ≠ 0 := pow_ne_zero n hp'.out.ne_zero
  set u : (AlgebraicClosure ℚ)ˣ := (hζ.isUnit hk).unit with hu
  have hζu : IsPrimitiveRoot u (p ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by
    rw [hu, IsUnit.unit_spec]; exact hζ)
  have h2 : u ^ a = u ^ b := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu, IsUnit.unit_spec, h1]
  have h3 : a ≡ b [MOD p ^ n] := by
    rw [hζu.eq_orderOf]
    exact pow_eq_pow_iff_modEq.mp h2
  obtain ⟨k, hk'⟩ := (Nat.modEq_iff_dvd.mp h3)
  rw [Ideal.mem_span_singleton']
  refine ⟨-(k : R), ?_⟩
  have : ((b : ℤ) : R) - ((a : ℤ) : R) = (((p ^ n : ℕ) : ℤ) : R) * ((k : ℤ) : R) := by
    rw [← Int.cast_sub, hk', Int.cast_mul]
  simp only [Int.cast_natCast] at this
  linear_combination this
  where hp' : Fact p.Prime := inferInstance

end Cyclotomic

theorem eq_zero_of_forall_mem_span_pow {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {q : R} (hq : q ∈ maximalIdeal R) {x : R} (hx : ∀ m : ℕ, x ∈ Ideal.span {q ^ m}) : x = 0 := by
  have hle : ∀ m : ℕ, Ideal.span {q ^ m} ≤ maximalIdeal R ^ m := fun m =>
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_mem_pow hq m)
  have hmem : x ∈ (⨅ m : ℕ, maximalIdeal R ^ m) := Ideal.mem_iInf.mpr fun m => hle m (hx m)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hmem

theorem map_mem_span {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {x q : R}
    (h : x ∈ Ideal.span {q}) : f x ∈ Ideal.span {f q} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  exact Ideal.mem_span_singleton'.mpr ⟨f y, by rw [← map_mul, hy]⟩

theorem isUnit_natCast_of_not_dvd {A : Type} [CommRing A] [IsLocalRing A]
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ maximalIdeal A) {u : ℕ} (hu : ¬ p ∣ u) :
    IsUnit (u : A) := by
  by_contra hcon
  have hmem : (u : A) ∈ maximalIdeal A := (mem_maximalIdeal _).mpr hcon
  have hcop : IsCoprime (p : ℤ) (u : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hu)
  obtain ⟨x, y, hxy⟩ := hcop
  have h1 : ((x : ℤ) : A) * (p : A) + ((y : ℤ) : A) * (u : A) = 1 := by
    have := congrArg (fun t : ℤ => (t : A)) hxy
    push_cast at this
    exact this
  apply (maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpA) (Ideal.mul_mem_left _ _ hmem)

theorem pow_dvd_of_natCast_mem_span {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CharZero A] {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ maximalIdeal A) {n z : ℕ}
    (hz : (z : A) ∈ Ideal.span {((p ^ n : ℕ) : A)}) : p ^ n ∣ z := by
  rcases Nat.eq_zero_or_pos z with rfl | hz0
  · exact dvd_zero _
  obtain ⟨m, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hz0.ne' p hp.one_lt.ne'
  have huA : IsUnit (u : A) := isUnit_natCast_of_not_dvd hp hpA hu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz

  have hnm : n ≤ m := by
    by_contra hlt
    push Not at hlt
    have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

    have h1 : (p : A) ^ m * ((u : A) - (p : A) ^ (n - m) * c) = 0 := by
      have h2 : (p : A) ^ n = (p : A) ^ m * (p : A) ^ (n - m) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      have h3 : c * (p : A) ^ n = (p : A) ^ m * (u : A) := by
        have := hc; push_cast at this; exact this
      rw [mul_sub, ← h3, h2]; ring
    have h4 : (u : A) - (p : A) ^ (n - m) * c = 0 :=
      (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hp0)
    have h5 : (u : A) = (p : A) ^ (n - m) * c := sub_eq_zero.mp h4
    have hmem : (u : A) ∈ maximalIdeal A := by
      rw [h5]
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
      rw [hk, show m + k + 1 - m = k + 1 by omega, pow_succ]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hpA)
    exact (mem_maximalIdeal _).mp hmem huA
  exact (pow_dvd_pow p hnm).mul_right u

theorem exists_smul_eq_and_notMem {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {V : Type} [AddCommGroup V] [Module A V] (b : Module.Basis (Fin 2) A V) {w : V} (hw : w ≠ 0) :
    ∃ (d : A) (w₀ : V), d ≠ 0 ∧ w = d • w₀ ∧ w₀ ∉ (maximalIdeal A) • (⊤ : Submodule A V) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have key : ∀ v : V, (IsUnit (b.repr v 0) ∨ IsUnit (b.repr v 1)) →
      v ∉ (maximalIdeal A) • (⊤ : Submodule A V) := by
    intro v hv hmem
    rcases hv with h | h
    · exact (mem_maximalIdeal _).mp (repr_mem_of_mem_smul_top (b := b) hmem 0) h
    · exact (mem_maximalIdeal _).mp (repr_mem_of_mem_smul_top (b := b) hmem 1) h
  have hw' : w = b.repr w 0 • b 0 + b.repr w 1 • b 1 := by
    have h := b.sum_repr w
    rw [Fin.sum_univ_two] at h
    exact h.symm
  have hrepr0 : ∀ (x y : A), b.repr (x • b 0 + y • b 1) 0 = x := by
    intro x y
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, b.repr_self,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul,
      mul_one, mul_zero, add_zero]
  have hrepr1 : ∀ (x y : A), b.repr (x • b 0 + y • b 1) 1 = y := by
    intro x y
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, b.repr_self,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul,
      mul_one, mul_zero, zero_add]
  by_cases h0 : b.repr w 0 = 0
  · have h1 : b.repr w 1 ≠ 0 := by
      intro h1
      apply hw
      rw [hw', h0, h1, zero_smul, zero_smul, add_zero]
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h1 hϖ
    refine ⟨ϖ ^ n, (0 : A) • b 0 + (u : A) • b 1, pow_ne_zero _ hϖ.ne_zero, ?_,
      key _ (Or.inr ?_)⟩
    · rw [hw', h0, hu, zero_smul, zero_add, smul_add, smul_zero, zero_add, smul_smul, mul_comm]
    · rw [hrepr1]; exact Units.isUnit u
  by_cases h1 : b.repr w 1 = 0
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    refine ⟨ϖ ^ n, (u : A) • b 0 + (0 : A) • b 1, pow_ne_zero _ hϖ.ne_zero, ?_,
      key _ (Or.inl ?_)⟩
    · rw [hw', h1, hu, zero_smul, add_zero, smul_add, smul_zero, add_zero, smul_smul, mul_comm]
    · rw [hrepr0]; exact Units.isUnit u
  obtain ⟨n0, u0, hu0⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  obtain ⟨n1, u1, hu1⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h1 hϖ
  rcases le_total n0 n1 with hle | hle
  · refine ⟨ϖ ^ n0, (u0 : A) • b 0 + ((u1 : A) * ϖ ^ (n1 - n0)) • b 1, pow_ne_zero _ hϖ.ne_zero,
      ?_, key _ (Or.inl ?_)⟩
    · rw [hw', hu0, hu1, smul_add, smul_smul, smul_smul]
      congr 1
      · rw [mul_comm]
      · congr 1
        rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hle]
    · rw [hrepr0]; exact Units.isUnit u0
  · refine ⟨ϖ ^ n1, ((u0 : A) * ϖ ^ (n0 - n1)) • b 0 + (u1 : A) • b 1, pow_ne_zero _ hϖ.ne_zero,
      ?_, key _ (Or.inr ?_)⟩
    · rw [hw', hu0, hu1, smul_add, smul_smul, smul_smul]
      congr 1
      · congr 1
        rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hle]
      · rw [mul_comm]
    · rw [hrepr1]; exact Units.isUnit u1

section Main

set_option maxHeartbeats 6400000 in

theorem main
    {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [CharZero A]
    [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (hinj : Function.Injective φ)
    (ρ : GaloisRepAdic A) (p : ℕ) (hp : p.Prime)
    (h : (ρ.baseChangeAlong φ hφ).IsStrictOrdinaryAt p) :
    ρ.IsStrictOrdinaryAt p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra A B := φ.toAlgebra
  haveI := hφ
  haveI : Module.Free B (B ⊗[A] ρ.V) := (ρ.baseChangeAlong φ hφ).instFree
  haveI : Module.Finite B (B ⊗[A] ρ.V) := (ρ.baseChangeAlong φ hφ).instFinite

  have hpB : (p : B) ∈ maximalIdeal B := h.1
  have hpA : (p : A) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (φ (p : A)) := hu.map φ
    rw [map_natCast] at h1
    exact (mem_maximalIdeal _).mp hpB h1
  refine ⟨hpA, fun P hP => ?_⟩
  have hID : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ P.inertiaSubgroupIn ℚ → σ ∈ P.decompositionSubgroup ℚ := by
    intro σ hσ
    obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.mp hσ
    exact τ.2

  have hst : ∃ Li : Submodule B (B ⊗[A] ρ.V),
      (∃ c : Module.Basis (Fin 2) B (B ⊗[A] ρ.V), Li = B ∙ c 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ u ∈ Li, (ρ.ρ σ).baseChange B u ∈ Li) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ u : B ⊗[A] ρ.V, (ρ.ρ σ).baseChange B u - u ∈ Li) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∃ x z : B,
        (∀ w ∈ Li, (ρ.ρ σ).baseChange B w = x • w) ∧
        (∀ u : B ⊗[A] ρ.V, (ρ.ρ σ).baseChange B u - z • u ∈ Li) ∧
        ∀ (m a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ m = 1 → σ μ = μ ^ a) →
          x - (a : B) * z ∈ Ideal.span {((p ^ m : ℕ) : B)}) :=
    h.2 P hP
  obtain ⟨Li, ⟨c, hc⟩, hD, hI, hS⟩ := hst
  rw [hc] at hD hI hS

  obtain ⟨τ, hτI, n₀, a₀, hτpow, ha₀⟩ := exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one p hp P hP
  have hτD : τ ∈ P.decompositionSubgroup ℚ := hID τ hτI
  set e : A := eps A p hpA τ with he_def
  have hea : e - (a₀ : A) ∈ Ideal.span {((p ^ n₀ : ℕ) : A)} := by
    obtain ⟨bm, hbm, hepsm⟩ := exists_pow_eq_and_eps_sub_mem A p hpA τ n₀
    have h3 := natCast_sub_natCast_mem_of_pow_eq p A τ n₀ bm a₀ hbm hτpow
    have : e - (a₀ : A) = (e - bm) + ((bm : A) - a₀) := by ring
    rw [this]
    exact Ideal.add_mem _ hepsm h3
  have he1 : e ≠ 1 := by
    intro h1
    apply ha₀
    rcases Nat.eq_zero_or_pos a₀ with h0 | hpos
    · subst h0
      have hmem : ((1 : ℕ) : A) ∈ Ideal.span {((p ^ n₀ : ℕ) : A)} := by
        rw [h1, Nat.cast_zero, sub_zero] at hea
        rwa [Nat.cast_one]
      have h2 : p ^ n₀ ∣ 1 := pow_dvd_of_natCast_mem_span hp hpA hmem
      rw [Nat.dvd_one] at h2
      rw [h2]
      exact Nat.modEq_one
    · have hmem : ((a₀ - 1 : ℕ) : A) ∈ Ideal.span {((p ^ n₀ : ℕ) : A)} := by
        have h2 : ((a₀ - 1 : ℕ) : A) = -(e - (a₀ : A)) := by
          rw [Nat.cast_sub hpos, Nat.cast_one, h1]; ring
        rw [h2]
        exact neg_mem hea
      have hdvd := pow_dvd_of_natCast_mem_span hp hpA hmem
      exact ((Nat.modEq_iff_dvd' hpos).mpr hdvd).symm

  obtain ⟨x', z', hx', hz', hcong⟩ := hS τ hτD
  have hz1 : z' = 1 := by
    have e1 := eq_zc_of_sub_smul_mem (hz' (c 1))
    have e2 : (1 : B) = zc c ((ρ.ρ τ).baseChange B) :=
      eq_zc_of_sub_smul_mem (by rw [one_smul]; exact hI τ hτI (c 1))
    rw [e1, ← e2]
  have hx'e : x' = φ e := by
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_mem_span_pow hpB
    intro m
    obtain ⟨bm, hbm, hepsm⟩ := exists_pow_eq_and_eps_sub_mem A p hpA τ m
    have h1 := hcong m bm hbm
    rw [hz1, mul_one, Nat.cast_pow] at h1
    have h2 : φ e - (bm : B) ∈ Ideal.span {(p : B) ^ m} := by
      have := map_mem_span φ hepsm
      simpa only [map_sub, map_natCast, Nat.cast_pow, map_pow] using this
    have h3 : x' - φ e = (x' - bm) - (φ e - bm) := by ring
    rw [h3]
    exact Ideal.sub_mem _ h1 h2
  have hφe1 : φ e ≠ 1 := fun h1 => he1 (hinj (by rw [h1, map_one]))

  set f : ρ.V →ₗ[A] ρ.V := ρ.ρ τ - e • LinearMap.id with hf_def
  have htmul_smul : ∀ (y : B) (v : ρ.V), y ⊗ₜ[A] (e • v) = φ e • (y ⊗ₜ[A] v) := by
    intro y v
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← smul_eq_mul,
      TensorProduct.smul_tmul']
    rfl
  have hfB : ∀ u : B ⊗[A] ρ.V, f.baseChange B u = (ρ.ρ τ).baseChange B u - φ e • u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero, sub_zero]
    | tmul y v =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hf_def, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_sub, htmul_smul]
    | add u v hu hv =>
      rw [map_add, map_add, hu, hv, smul_add]
      abel
  have hfc0 : f.baseChange B (c 0) = 0 := by
    rw [hfB, hx' _ (Submodule.mem_span_singleton_self _), hx'e, sub_self]
  have hdetB : LinearMap.det (f.baseChange B) = 0 := by
    refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ?_
    rw [Submodule.ne_bot_iff]
    exact ⟨c 0, LinearMap.mem_ker.mpr hfc0, c.ne_zero 0⟩
  have hdet : LinearMap.det f = 0 := by
    apply hinj
    rw [map_zero, ← hdetB, LinearMap.det_baseChange]
    rfl
  obtain ⟨w, hwker, hw0⟩ :=
    (LinearMap.ker f).ne_bot_iff.mp (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet)
  obtain ⟨d, w₀, hd, hww₀, hw₀⟩ :=
    exists_smul_eq_and_notMem (Module.finBasisOfFinrankEq A ρ.V ρ.finrank_eq) hw0
  have hfw₀ : f w₀ = 0 := by
    have h1 : d • f w₀ = 0 := by
      rw [← map_smul, ← hww₀]
      exact LinearMap.mem_ker.mp hwker
    exact (smul_eq_zero.mp h1).resolve_left hd
  have hρw₀ : ρ.ρ τ w₀ = e • w₀ := by
    have h1 := hfw₀
    rw [hf_def, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply] at h1
    exact h1

  obtain ⟨b, hb0⟩ := exists_basis_of_notMem (Module.finBasisOfFinrankEq A ρ.V ρ.finrank_eq) w₀ hw₀
  set bB : Module.Basis (Fin 2) B (B ⊗[A] ρ.V) := Algebra.TensorProduct.basis B b with hbB_def
  have hbB : ∀ j, bB j = (1 : B) ⊗ₜ[A] b j := fun j => Algebra.TensorProduct.basis_apply b j
  have hmem : bB 0 ∈ B ∙ c 0 := by
    have h1 : (ρ.ρ τ).baseChange B (bB 0) = φ e • bB 0 := by
      rw [hbB, hb0, LinearMap.baseChange_tmul, hρw₀, htmul_smul]
    have h2 := hz' (bB 0)
    rw [hz1, h1] at h2
    have h2' : (φ e - 1) • bB 0 ∈ B ∙ c 0 := by
      have e3 : (φ e - 1) • bB 0 = φ e • bB 0 - (1 : B) • bB 0 := sub_smul (φ e) (1 : B) (bB 0)
      rw [e3]
      convert h2 using 2
    have h3 := repr_one_eq_zero_of_mem c h2'
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_eq_zero] at h3
    rcases h3 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hφe1
    · exact mem_of_repr_one_eq_zero c h3
  have hLi : B ∙ c 0 = B ∙ bB 0 := span_eq_span_of_mem hmem bB rfl
  rw [hLi] at hD hI hS

  have hcoord : ∀ (u : ρ.V) (j : Fin 2), bB.repr ((1 : B) ⊗ₜ[A] u) j = φ (b.repr u j) := by
    intro u j
    rw [hbB_def, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
    rfl
  have hmemiff : ∀ u : ρ.V, u ∈ A ∙ b 0 ↔ (1 : B) ⊗ₜ[A] u ∈ B ∙ bB 0 := by
    intro u
    rw [mem_iff_repr_one_eq_zero, mem_iff_repr_one_eq_zero, hcoord]
    constructor
    · intro hu
      rw [hu, map_zero]
    · intro hu
      exact hinj (by rw [hu, map_zero])
  have hPresD : ∀ σ ∈ P.decompositionSubgroup ℚ, Pres b (ρ.ρ σ) := by
    intro σ hσ u hu
    rw [hmemiff] at hu ⊢
    have h1 := hD σ hσ _ hu
    rw [LinearMap.baseChange_tmul] at h1
    exact h1
  refine ⟨A ∙ b 0, ⟨b, rfl⟩, hPresD, ?_, ?_⟩
  ·
    intro σ hσ u
    rw [hmemiff]
    have h1 := hI σ hσ ((1 : B) ⊗ₜ[A] u)
    rw [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub] at h1
    exact h1
  ·
    intro σ hσ
    have hPres : Pres b (ρ.ρ σ) := hPresD σ hσ
    set x : A := xc b (ρ.ρ σ) with hx
    set z : A := zc b (ρ.ρ σ) with hz
    refine ⟨x, z, fun u hu => apply_eq_xc_smul hPres hu, fun u => sub_zc_smul_mem hPres u, ?_⟩

    have happ : ∀ j : Fin 2, (ρ.ρ σ).baseChange B (bB j) = (1 : B) ⊗ₜ[A] (ρ.ρ σ (b j)) := by
      intro j
      rw [hbB, LinearMap.baseChange_tmul]
    have hxB : xc bB ((ρ.ρ σ).baseChange B) = φ x := by
      show bB.repr _ 0 = _
      rw [happ, hcoord]
      rfl
    have hzB : zc bB ((ρ.ρ σ).baseChange B) = φ z := by
      show bB.repr _ 1 = _
      rw [happ, hcoord]
      rfl

    have hcongB : ∀ (m a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ m = 1 → σ μ = μ ^ a) →
        φ x - (a : B) * φ z ∈ Ideal.span {((p ^ m : ℕ) : B)} := by
      intro m a hσa
      obtain ⟨x'', z'', hx'', hz'', hcong''⟩ := hS σ hσ
      have hPresB : Pres bB ((ρ.ρ σ).baseChange B) := fun u hu => hD σ hσ u hu
      have hx''eq : x'' = xc bB ((ρ.ρ σ).baseChange B) :=
        eq_xc_of_apply_eq_smul (hx'' _ (Submodule.mem_span_singleton_self _))
      have hz''eq : z'' = zc bB ((ρ.ρ σ).baseChange B) := eq_zc_of_sub_smul_mem (hz'' (bB 1))
      rw [← hxB, ← hzB, ← hx''eq, ← hz''eq]
      exact hcong'' m a hσa

    have hexact : x - eps A p hpA σ * z = 0 := by
      apply hinj
      rw [map_zero, map_sub, map_mul]
      apply eq_zero_of_forall_mem_span_pow hpB
      intro m
      obtain ⟨bm, hbm, hepsm⟩ := exists_pow_eq_and_eps_sub_mem A p hpA σ m
      have h1 := hcongB m bm hbm
      rw [Nat.cast_pow] at h1
      have h2 : φ (eps A p hpA σ) - (bm : B) ∈ Ideal.span {(p : B) ^ m} := by
        have := map_mem_span φ hepsm
        simpa only [map_sub, map_natCast, Nat.cast_pow, map_pow] using this
      have h3 : φ x - φ (eps A p hpA σ) * φ z =
          (φ x - (bm : B) * φ z) - (φ (eps A p hpA σ) - (bm : B)) * φ z := by ring
      rw [h3]
      exact Ideal.sub_mem _ h1 (Ideal.mul_mem_right _ _ h2)
    intro m a hσa
    obtain ⟨bm, hbm, hepsm⟩ := exists_pow_eq_and_eps_sub_mem A p hpA σ m
    have h1 : eps A p hpA σ - (a : A) ∈ Ideal.span {((p ^ m : ℕ) : A)} := by
      have h3 := natCast_sub_natCast_mem_of_pow_eq p A σ m bm a hbm hσa
      have : eps A p hpA σ - (a : A) = (eps A p hpA σ - (bm : A)) + ((bm : A) - (a : A)) := by ring
      rw [this]
      exact Ideal.add_mem _ hepsm h3
    have hxeq : x = eps A p hpA σ * z := sub_eq_zero.mp hexact
    have h2 : x - (a : A) * z = (eps A p hpA σ - (a : A)) * z := by rw [hxeq]; ring
    rw [h2]
    exact Ideal.mul_mem_right _ _ h1

end Main

end DescStrAsm
p2m_reactivate "P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_isStrictOrdinaryAt_baseChangeAlong_of_injective.DescStrAsm"

theorem solution
    {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharZero A]
    [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (hinj : Function.Injective φ)
    (ρ : GaloisRepAdic A) (p : ℕ) (hp : p.Prime)
    (h : (ρ.baseChangeAlong φ hφ).IsStrictOrdinaryAt p) :
    ρ.IsStrictOrdinaryAt p :=
  DescStrAsm.main φ hφ hinj ρ p hp h

end S_GaloisRepAdic_isStrictOrdinaryAt_of_isStrictOrdinaryAt_baseChangeAlong_of_injective
end P2MW
export P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_isStrictOrdinaryAt_baseChangeAlong_of_injective (solution)
