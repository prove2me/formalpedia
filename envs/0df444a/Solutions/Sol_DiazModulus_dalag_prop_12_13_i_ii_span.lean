-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_13_i_ii_span
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:24:42.765065+00:00
-- url     : https://prove2.me/submissions/22eba5b3-6175-48d9-a482-3c050a6e2b22

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # DALAG Prop. 12.13, (i) ⇒ (ii) in span form

Write each `xᵢ = cᵢ + zᵢ` with `cᵢ ∈ k` and `zᵢ = Σⱼ fᵢⱼ bⱼ` in the `k`-span of the `bⱼ`, the coefficient rows
`fᵢ` being finitely supported. Since `1, x₁, …, xₙ` are `k`-free, so are the `zᵢ`, hence so are the rows `fᵢ`.
Extending the coordinate functionals of the basis `(fᵢ)` of their span gives linear forms `φₗ` with
`φₗ(fᵢ) = δᵢₗ`. The affine substitution `σ : k[X₁, …, Xₙ] → k[Yⱼ]`, `Xᵢ ↦ cᵢ + Σⱼ fᵢⱼ Yⱼ`, has the explicit
left inverse `τ : Yⱼ ↦ Σₗ φₗ(eⱼ)(Xₗ − cₗ)`, so `σ` is injective. Evaluation at `x` is evaluation at `b` composed
with `σ`, and evaluation at `b` is injective since `b` is algebraically independent; hence evaluation at `x` is
injective, that is, `x` is algebraically independent over `k`. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*}
    (b : ι → K) (hb : AlgebraicIndependent k b) {n : ℕ} (x : Fin n → K)
    (hxE : ∀ i, x i ∈ Submodule.span k (insert (1 : K) (Set.range b)))
    (hx : LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K)) :
    AlgebraicIndependent k x := by
  classical
  -- x i = c i • 1 + z i, z i = Σ f i j • b j
  choose c z hz hxcz using fun i => Submodule.mem_span_insert.1 (hxE i)
  choose f hf using fun i => (Finsupp.mem_span_range_iff_exists_finsupp).1 (hz i)
  have hzf : ∀ i, z i = Finsupp.linearCombination k b (f i) := fun i => by
    rw [Finsupp.linearCombination_apply, hf i]
  -- the z i are k-free, hence so are the rows f i
  have hzli : LinearIndependent k z := by
    rw [Fintype.linearIndependent_iff] at hx ⊢
    intro g hg i
    have h0 := hx (Fin.cons (-∑ l, g l * c l) g) (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hxcz, smul_add, Finset.sum_add_distrib, hg, add_zero,
        smul_smul, ← Finset.sum_smul, neg_smul, neg_add_cancel])
    simpa using h0 i.succ
  have hfli : LinearIndependent k f :=
    LinearIndependent.of_comp (Finsupp.linearCombination k b) (by
      convert hzli using 1; funext i; exact (hzf i).symm)
  -- dual functionals: φ (f i) = Pi.single i 1
  let B := Module.Basis.span hfli
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (B.equivFun.toLinearMap : _ →ₗ[k] (Fin n → k))
  have hφf : ∀ i, φ (f i) = Pi.single i 1 := fun i => by
    have := LinearMap.congr_fun hφ (B i)
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at this
    ext l
    have h2 := congrFun this l
    rw [Module.Basis.equivFun_self, Module.Basis.span_apply] at h2
    rw [h2]; simp [Pi.single_apply, eq_comm]
  -- σ and its left inverse τ
  let σ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial ι k := MvPolynomial.aeval fun i =>
    MvPolynomial.C (c i) + (f i).sum fun j a => MvPolynomial.C a * MvPolynomial.X j
  let τ : MvPolynomial ι k →ₐ[k] MvPolynomial (Fin n) k := MvPolynomial.aeval fun j =>
    ∑ l, MvPolynomial.C (φ (Finsupp.single j 1) l) * (MvPolynomial.X l - MvPolynomial.C (c l))
  have hτσ : τ.comp σ = AlgHom.id k _ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    have key : ∀ l, ((f i).sum fun j a => a * φ (Finsupp.single j 1) l) = if i = l then 1 else 0 := by
      intro l
      have e : f i = (f i).sum fun j a => a • Finsupp.single j (1 : k) := by
        simp only [Finsupp.smul_single_one, Finsupp.sum_single]
      have := congrFun (hφf i) l
      rw [e, map_finsuppSum] at this
      simp only [Finsupp.sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [Finsupp.sum, this]
      simp [Pi.single_apply, eq_comm]
    simp only [σ, τ, AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply, Finsupp.sum, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← MvPolynomial.C_mul, ← Finset.sum_mul, ← map_sum]
    have key' : ∀ l, (∑ j ∈ (f i).support, f i j * φ (Finsupp.single j 1) l) = if i = l then 1 else 0 :=
      fun l => key l
    simp only [key', apply_ite MvPolynomial.C, map_one, map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hσinj : Function.Injective σ :=
    Function.LeftInverse.injective (g := τ) fun p => by rw [← AlgHom.comp_apply, hτσ, AlgHom.id_apply]
  have hcomp : (MvPolynomial.aeval b).comp σ = MvPolynomial.aeval x := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [σ, AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, MvPolynomial.aeval_C, Finsupp.sum,
      map_sum, map_mul]
    rw [hxcz, hzf, Finsupp.linearCombination_apply, Finsupp.sum, Algebra.smul_def, mul_one]
    simp [Algebra.smul_def]
  rw [algebraicIndependent_iff_injective_aeval] at hb ⊢
  rw [← hcomp]
  exact hb.comp hσinj
