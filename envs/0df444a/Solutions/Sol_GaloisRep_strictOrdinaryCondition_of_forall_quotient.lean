-- Prove2me | solution 1 for GaloisRep.strictOrdinaryCondition_of_forall_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/61ef5eaf-8d6a-5dda-a1f3-7ea69bb9456e

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_forall_quotient
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_forall_quotient
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_forall_quotient
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_strictOrdinaryCondition_of_forall_quotient

set_option autoImplicit false

open scoped TensorProduct
open IsLocalRing

namespace S4Aux

section Quotients

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem maximalIdeal_pow_succ_ne_top (m : ℕ) : maximalIdeal A ^ (m + 1) ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self m.succ_ne_zero))

scoped instance nontrivial_quotient_maximalIdeal_pow_succ (m : ℕ) :
    Nontrivial (A ⧸ maximalIdeal A ^ (m + 1)) :=
  Ideal.Quotient.nontrivial_iff.mpr (maximalIdeal_pow_succ_ne_top m)

scoped instance isLocalRing_quotient_maximalIdeal_pow_succ (m : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (m + 1)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isLocalHom_mk_maximalIdeal_pow_succ (m : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (m + 1))) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

variable [IsNoetherianRing A]

theorem mem_of_forall_mem_sup_pow (I : Ideal A) {x : A}
    (hx : ∀ m : ℕ, x ∈ I ⊔ maximalIdeal A ^ (m + 1)) : x ∈ I := by
  classical
  by_cases hI : I = ⊤
  · rw [hI]; exact Submodule.mem_top
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let J : Ideal (A ⧸ I) := (maximalIdeal A).map (Ideal.Quotient.mk I)
  have hJ : J ≤ maximalIdeal (A ⧸ I) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit (Ideal.Quotient.mk I) a ha
  have hJtop : J ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hJ
  have hxJ : ∀ m : ℕ, Ideal.Quotient.mk I x ∈ J ^ (m + 1) := by
    intro m
    have : Ideal.Quotient.mk I x ∈ (I ⊔ maximalIdeal A ^ (m + 1)).map (Ideal.Quotient.mk I) :=
      Ideal.mem_map_of_mem _ (hx m)
    rwa [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow] at this
  have hx' : Ideal.Quotient.mk I x ∈ ⨅ m : ℕ, J ^ m :=
    Ideal.mem_iInf.mpr fun m => (Ideal.pow_le_pow_right m.le_succ) (hxJ m)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJtop, Ideal.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem] at hx'
  exact hx'

end Quotients

section Basis

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem repr_one_eq_zero_of_mem (e : Module.Basis (Fin 2) R W) {v : W} (hv : v ∈ R ∙ e 0) :
    e.repr v 1 = 0 := by
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hv
  simp

theorem eq_zero_of_smul_one_mem (e : Module.Basis (Fin 2) R W) {c : R} (h : c • e 1 ∈ R ∙ e 0) :
    c = 0 := by
  have := repr_one_eq_zero_of_mem e h
  simpa using this

theorem eq_of_smul_zero_eq (e : Module.Basis (Fin 2) R W) {c d : R} (h : c • e 0 = d • e 0) :
    c = d := by
  have := congrArg (fun w => e.repr w 0) h
  simpa using this

theorem eq_coords (e : Module.Basis (Fin 2) R W) (v : W) :
    v = e.repr v 0 • e 0 + e.repr v 1 • e 1 := by
  conv_lhs => rw [← e.sum_repr v]
  rw [Fin.sum_univ_two]

theorem det_eq_of_triangular (e : Module.Basis (Fin 2) R W) (f : W →ₗ[R] W) (x y z : R)
    (h0 : f (e 0) = x • e 0) (h1 : f (e 1) = y • e 0 + z • e 1) : LinearMap.det f = x * z := by
  classical
  rw [← LinearMap.det_toMatrix e, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, h0, h1]

theorem exists_coords (e : Module.Basis (Fin 2) R W) (f : W →ₗ[R] W) (hD : f (e 0) ∈ R ∙ e 0) :
    ∃ x y z : R, f (e 0) = x • e 0 ∧ f (e 1) = y • e 0 + z • e 1 := by
  refine ⟨e.repr (f (e 0)) 0, e.repr (f (e 1)) 0, e.repr (f (e 1)) 1, ?_, eq_coords e _⟩
  have h := eq_coords e (f (e 0))
  rw [repr_one_eq_zero_of_mem e hD, zero_smul, add_zero] at h
  exact h

theorem sub_smul_mem_of_coords (e : Module.Basis (Fin 2) R W) (f : W →ₗ[R] W) {x y z : R}
    (h0 : f (e 0) = x • e 0) (h1 : f (e 1) = y • e 0 + z • e 1) (v : W) :
    f v - z • v ∈ R ∙ e 0 := by
  have key : ∀ c0 c1 : R,
      f (c0 • e 0 + c1 • e 1) - z • (c0 • e 0 + c1 • e 1) ∈ R ∙ e 0 := by
    intro c0 c1
    have eq : f (c0 • e 0 + c1 • e 1) - z • (c0 • e 0 + c1 • e 1) =
        (c0 * x + c1 * y - z * c0) • e 0 := by
      rw [map_add, map_smul, map_smul, h0, h1]
      module
    rw [eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hv := eq_coords e v
  rw [hv]
  exact key _ _

theorem span_eq_range_of_isUnit (e : Module.Basis (Fin 2) R W) (f : W →ₗ[R] W)
    (hD : f (e 0) ∈ R ∙ e 0) (hI : ∀ v, f v - v ∈ R ∙ e 0)
    (hu : IsUnit (LinearMap.det f - 1)) :
    (R ∙ e 0) = LinearMap.range (f - 1) := by
  obtain ⟨x, y, z, h0, h1⟩ := exists_coords e f hD
  have hz : z = 1 := by
    have h := hI (e 1)
    rw [h1] at h
    have h' := Submodule.sub_mem _ h
      (Submodule.smul_mem _ y (Submodule.mem_span_singleton_self (e 0)))
    have eq : y • e 0 + z • e 1 - e 1 - y • e 0 = (z - 1) • e 1 := by module
    rw [eq] at h'
    exact sub_eq_zero.mp (eq_zero_of_smul_one_mem e h')
  rw [det_eq_of_triangular e f x y z h0 h1, hz, mul_one] at hu
  obtain ⟨u, hu'⟩ := hu
  have hfe : (f - 1) (e 0) = (x - 1) • e 0 := by
    rw [LinearMap.sub_apply, Module.End.one_apply, h0, sub_smul, one_smul]
  apply le_antisymm
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨((u⁻¹ : Rˣ) : R) • e 0, ?_⟩
    rw [map_smul, hfe, smul_smul, ← hu', Units.inv_mul, one_smul]
  · rintro _ ⟨v, rfl⟩
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact hI v

end Basis

section Galois

theorem inertiaSubgroupIn_le_decompositionSubgroup {K L : Type} [Field K] [Field L]
    [Algebra K L] (P : ValuationSubring L) :
    P.inertiaSubgroupIn K ≤ P.decompositionSubgroup K := by
  intro σ hσ
  obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.mp hσ
  exact τ.2

theorem exists_mem_inertiaSubgroupIn_apply_eq_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ 2 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h2 : ((ZMod.unitOfCoprime 2 hcop : (ZMod p)ˣ) : ZMod p).val = 2 := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt (lt_of_le_of_ne hp.two_le (Ne.symm hp2))]
  obtain ⟨σ, hσ, h⟩ := P.exists_mem_inertiaSubgroupIn_apply_eq_pow hp hP
    (ZMod.unitOfCoprime 2 hcop)
  refine ⟨σ, hσ, fun μ hμ => ?_⟩
  have h' := h μ hμ
  rwa [h2] at h'

theorem isUnit_sub_one_of_sub_two_mem {B : Type} [CommRing B] [IsLocalRing B] {p : ℕ}
    (hp : (p : B) ∈ maximalIdeal B) {d : B} (hd : d - 2 ∈ Ideal.span {(p : B)}) :
    IsUnit (d - 1) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hd
  have hm : d - 2 ∈ maximalIdeal B := hc ▸ Ideal.mul_mem_left _ c hp
  by_contra hnu
  have h1 : d - 1 ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h : (1 : B) ∈ maximalIdeal B := by
    have e : (1 : B) = (d - 1) - (d - 2) := by ring
    rw [e]
    exact (maximalIdeal B).sub_mem h1 hm
  exact (maximalIdeal B).ne_top_iff_one.mp (Ideal.IsMaximal.ne_top inferInstance) h

variable {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B]

theorem det_baseChangeAlong_apply (f : A →+* B) (hf : IsLocalHom f) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.baseChangeAlong f hf).ρ σ) = f (LinearMap.det (ρ.ρ σ)) := by
  letI := f.toAlgebra
  exact LinearMap.det_baseChange (ρ.ρ σ)

theorem level (f : A →+* B) (hf : IsLocalHom f) (ρ : GaloisRepAdic A) {p : ℕ}
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hdetB : (ρ.baseChangeAlong f hf).DetIsCyclotomic p)
    (hstr : (ρ.baseChangeAlong f hf).IsStrictOrdinaryAt p)
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ₀I : σ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hσ₀ : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ₀ μ = μ ^ 2)
    (b : Module.Basis (Fin 2) A ρ.V)
    (hD : ∀ σ ∈ P.decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ A ∙ b 0)
    (hI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ A ∙ b 0)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.decompositionSubgroup ℚ)
    {x y z : A} (h0 : ρ.ρ σ (b 0) = x • b 0) (h1 : ρ.ρ σ (b 1) = y • b 0 + z • b 1)
    (n a : ℕ) (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) :
    f (x - (a : A) * z) ∈ Ideal.span {((p ^ n : ℕ) : B)} := by
  classical
  letI : Algebra A B := f.toAlgebra

  have hdet2 : LinearMap.det ((ρ.ρ σ₀).baseChange B) - ((2 : ℕ) : B) ∈
      Ideal.span {((p ^ 1 : ℕ) : B)} :=
    hdetB.2 1 σ₀ 2 (fun μ hμ => hσ₀ μ (by rwa [pow_one] at hμ))
  obtain ⟨L', hL'ex, hD', hI', hsc'⟩ := hstr.2 P hP
  obtain ⟨b', hL'⟩ := hL'ex
  let L'' : Submodule B (B ⊗[A] ρ.V) := L'
  let b'' : Module.Basis (Fin 2) B (B ⊗[A] ρ.V) := b'
  have hL'' : L'' = B ∙ b'' 0 := hL'
  have hD'' : ∀ τ ∈ P.decompositionSubgroup ℚ, ∀ v : B ⊗[A] ρ.V, v ∈ L'' →
      (ρ.ρ τ).baseChange B v ∈ L'' := hD'
  have hI'' : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : B ⊗[A] ρ.V,
      (ρ.ρ τ).baseChange B v - v ∈ L'' := hI'
  have hsc'' : ∀ τ ∈ P.decompositionSubgroup ℚ, ∃ x' z' : B,
      (∀ w : B ⊗[A] ρ.V, w ∈ L'' → (ρ.ρ τ).baseChange B w = x' • w) ∧
      (∀ v : B ⊗[A] ρ.V, (ρ.ρ τ).baseChange B v - z' • v ∈ L'') ∧
      ∀ (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → τ μ = μ ^ a) →
        x' - (a : B) * z' ∈ Ideal.span {((p ^ n : ℕ) : B)} := hsc'

  let e : Module.Basis (Fin 2) B (B ⊗[A] ρ.V) := Algebra.TensorProduct.basis B b
  have he : ∀ i, e i = (1 : B) ⊗ₜ[A] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have hr : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : B) (v : ρ.V),
      (ρ.ρ τ).baseChange B (c ⊗ₜ[A] v) = c ⊗ₜ[A] ρ.ρ τ v := fun τ c v =>
    LinearMap.baseChange_tmul _ _ _
  have hsm : ∀ (a' : A) (w : ρ.V),
      ((1 : B) ⊗ₜ[A] (a' • w) : B ⊗[A] ρ.V) = f a' • ((1 : B) ⊗ₜ[A] w) := by
    intro a' w
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
      Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]
  have hline : ∀ (c : B) (ℓ : ρ.V), ℓ ∈ A ∙ b 0 → c ⊗ₜ[A] ℓ ∈ B ∙ e 0 := by
    intro c ℓ hℓ
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hℓ
    have : (c ⊗ₜ[A] (d • b 0) : B ⊗[A] ρ.V) = (d • c) • e 0 := by
      rw [he, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hIB : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ w : B ⊗[A] ρ.V,
      (ρ.ρ τ).baseChange B w - w ∈ B ∙ e 0 := by
    intro τ hτ w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero ((ρ.ρ τ).baseChange B), sub_zero]; exact Submodule.zero_mem _
    | tmul c v =>
      rw [hr, ← TensorProduct.tmul_sub]
      exact hline c _ (hI τ hτ v)
    | add u w hu hw =>
      rw [map_add ((ρ.ρ τ).baseChange B), add_sub_add_comm]
      exact Submodule.add_mem _ hu hw
  have hDB : ∀ τ ∈ P.decompositionSubgroup ℚ, (ρ.ρ τ).baseChange B (e 0) ∈ B ∙ e 0 := by
    intro τ hτ
    have h := hline 1 _ (hD τ hτ)
    rwa [← hr, ← he] at h
  have h0B : (ρ.ρ σ).baseChange B (e 0) = f x • e 0 := by rw [he, hr, h0, hsm]
  have h1B : (ρ.ρ σ).baseChange B (e 1) = f y • e 0 + f z • e 1 := by
    rw [he, he, hr, h1, TensorProduct.tmul_add, hsm, hsm]

  have hσ₀D : σ₀ ∈ P.decompositionSubgroup ℚ :=
    inertiaSubgroupIn_le_decompositionSubgroup P hσ₀I
  have hu : IsUnit (LinearMap.det ((ρ.ρ σ₀).baseChange B) - 1) := by
    rw [pow_one, Nat.cast_ofNat] at hdet2
    exact isUnit_sub_one_of_sub_two_mem hdetB.1 hdet2
  have hLB : (B ∙ e 0) = LinearMap.range ((ρ.ρ σ₀).baseChange B - 1) :=
    span_eq_range_of_isUnit e _ (hDB σ₀ hσ₀D) (hIB σ₀ hσ₀I) hu
  have hD'0 : (ρ.ρ σ₀).baseChange B (b'' 0) ∈ B ∙ b'' 0 := by
    have := hD'' σ₀ hσ₀D (b'' 0) (by rw [hL'']; exact Submodule.mem_span_singleton_self _)
    rwa [hL''] at this
  have hI'0 : ∀ v : B ⊗[A] ρ.V, (ρ.ρ σ₀).baseChange B v - v ∈ B ∙ b'' 0 := fun v => by
    have := hI'' σ₀ hσ₀I v
    rwa [hL''] at this
  have hL'B : L'' = LinearMap.range ((ρ.ρ σ₀).baseChange B - 1) := by
    rw [hL'']
    exact span_eq_range_of_isUnit b'' _ hD'0 hI'0 hu
  have hLL : L'' = B ∙ e 0 := hL'B.trans hLB.symm

  obtain ⟨x', z', hx', hz', hc'⟩ := hsc'' σ hσ
  have hx'x : x' = f x := by
    have := hx' (e 0) (by rw [hLL]; exact Submodule.mem_span_singleton_self _)
    rw [h0B] at this
    exact (eq_of_smul_zero_eq e this).symm
  have hz'z : z' = f z := by
    have h1' := hz' (e 1)
    rw [hLL, h1B] at h1'
    have h2' := Submodule.sub_mem _ h1'
      (Submodule.smul_mem _ (f y) (Submodule.mem_span_singleton_self (e 0)))
    have eq : f y • e 0 + f z • e 1 - z' • e 1 - f y • e 0 = (f z - z') • e 1 := by module
    rw [eq] at h2'
    exact (sub_eq_zero.mp (eq_zero_of_smul_one_mem e h2')).symm
  have hc := hc' n a ha
  rw [hx'x, hz'z] at hc
  rw [map_sub, map_mul, map_natCast]
  exact hc

end Galois

end S4Aux
p2m_reactivate "P2MW.S_GaloisRep_strictOrdinaryCondition_of_forall_quotient.S4Aux"

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      GaloisRep.strictOrdinaryCondition 𝒪 p S
        (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective))) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S ρ := by
  classical

  have hq : ∀ m : ℕ, GaloisRep.strictOrdinaryCondition 𝒪 p S
      (ρ.baseChangeAlong (Ideal.Quotient.mk (maximalIdeal A ^ (m + 1)))
        (S4Aux.isLocalHom_mk_maximalIdeal_pow_succ m)) := h
  have hdetA : ρ.DetIsCyclotomic p :=
    GaloisRepAdic.detIsCyclotomic_of_forall_quotient ρ fun m => (h m).1
  have hordA : ρ.IsOrdinaryAt p :=
    GaloisRepAdic.isOrdinaryAt_of_forall_quotient ρ hp hp2 (fun m => (h m).1)
      fun m => (h m).2.1.isOrdinaryAt
  refine ⟨hdetA, ⟨hdetA.1, fun P hP => ?_⟩, fun q hq' hqS =>
    GaloisRepAdic.isUnramifiedAt_of_forall_quotient ρ fun m => (h m).2.2 q hq' hqS⟩
  obtain ⟨L, ⟨b, hL⟩, hD, hI⟩ := hordA P hP
  refine ⟨L, ⟨b, hL⟩, hD, hI, fun σ hσ => ?_⟩
  have hD0 : ∀ τ ∈ P.decompositionSubgroup ℚ, ρ.ρ τ (b 0) ∈ A ∙ b 0 := fun τ hτ => by
    have := hD τ hτ (b 0) (by rw [hL]; exact Submodule.mem_span_singleton_self _)
    rwa [hL] at this
  have hI0 : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ A ∙ b 0 := fun τ hτ v => by
    have := hI τ hτ v
    rwa [hL] at this
  obtain ⟨x, y, z, h0, h1⟩ := S4Aux.exists_coords b (ρ.ρ σ) (hD0 σ hσ)
  refine ⟨x, z, fun w hw => ?_, fun v => ?_, fun n a ha => ?_⟩
  · rw [hL] at hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, h0, smul_comm]
  · rw [hL]
    exact S4Aux.sub_smul_mem_of_coords b (ρ.ρ σ) h0 h1 v
  ·
    obtain ⟨σ₀, hσ₀I, hσ₀⟩ := S4Aux.exists_mem_inertiaSubgroupIn_apply_eq_sq hp hp2 P hP
    refine S4Aux.mem_of_forall_mem_sup_pow _ fun m => ?_
    have hm := S4Aux.level (Ideal.Quotient.mk (maximalIdeal A ^ (m + 1)))
      (S4Aux.isLocalHom_mk_maximalIdeal_pow_succ m) ρ P hP (hq m).1 (hq m).2.1 hσ₀I hσ₀ b
      hD0 hI0 hσ h0 h1 n a ha
    have hspan : Ideal.span {((p ^ n : ℕ) : A ⧸ maximalIdeal A ^ (m + 1))} =
        (Ideal.span {((p ^ n : ℕ) : A)}).map (Ideal.Quotient.mk (maximalIdeal A ^ (m + 1))) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [hspan, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hm
    exact hm

end S_GaloisRep_strictOrdinaryCondition_of_forall_quotient
end P2MW
export P2MW.S_GaloisRep_strictOrdinaryCondition_of_forall_quotient (solution)
