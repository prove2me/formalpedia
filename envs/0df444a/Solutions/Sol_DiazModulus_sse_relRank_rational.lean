-- Prove2me | solution 1 for DiazModulus.sse_relRank_rational
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:12:16.805543+00:00
-- url     : https://prove2.me/submissions/fbee4469-fb0f-4b07-bbf8-979e3e7372f0

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_sse_independence_facts
import Theorems.Thm_DiazModulus_intMatrix_ker_facts

open Complex ComplexConjugate

/-! # The relation rank in the rational case `T ≤ ℂx`
Write `Υ(u, v)_i = u_i + Σ_k ω_k v_{(k,i)}` and `T = Υ(V' × L₁) ≤ ℂx`.
First `L₁ = 0`. If `v ∈ ℚ^{m×2}` is a rational kernel vector of `φ`, then `(0, v) ∈ V' × L₁`, so
`Υ(0, v) = c x`; the vector `Υ(0, v)` is algebraic, so `c = 0` by the second part of
`sse_independence_facts` (with `β = 1`), and `Σ_k ω_k v_{(k,i)} = 0` forces `v = 0` because `ω` is
ℚ-free. So `φ` has no rational kernel, hence no complex kernel (`intMatrix_ker_facts`), and
`L₁ = 0`. Next, for `s` in the relation set, `exp(Σ_i φ_{ki} z_i) = 1` with
`z = Σ_j s_j (η_j).2`, so `z = 2πi r` with `r` rational (`intMatrix_ker_facts`). The vector
`ζ₁ = Σ_j s_j (η_j).1` lies in `V' ≤ T ≤ ℂx` and is algebraic, so `ζ₁ = 0`. Then
`(Σ_j s_j ω_{j.1} y_{j.2}) x = Υ(Σ_j s_j η_j) = 2πi (Σ_k ω_k r_{(k,·)})`, an algebraic vector times
`2πi ≠ 0`, so the coefficient is `0` and `s = 0` (`sse_independence_facts`). The relation set is
`{0}`, and its ℚ-span has rank `0`. -/

namespace C14_S8
open DiazModulus

noncomputable def Ups (m : ℕ) (ω : Fin m → ℂ) :
    ((Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi fun i : Fin 2 =>
    (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
    + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)

theorem Ups_apply {m : ℕ} (ω : Fin m → ℂ) (z : (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) (i : Fin 2) :
    Ups m ω z i = z.1 i + ∑ k, ω k * z.2 (k, i) := by
  simp [Ups, LinearMap.sum_apply]

theorem Ups_inl {m : ℕ} (ω : Fin m → ℂ) (u : Fin 2 → ℂ) : Ups m ω (u, 0) = u := by
  ext i; simp [Ups_apply]

theorem prod_exp {N ι : Type*} [Fintype N] [Fintype ι] (a : N → ι → ℂ) (s : N → ℤ) (φ : ι → ℤ) :
    ∏ i, (∏ j, Complex.exp (a j i) ^ s j) ^ φ i
      = Complex.exp (∑ i, (φ i : ℂ) * ∑ j, (s j : ℂ) * a j i) := by
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum]

theorem main (m : ℕ) (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (hηΥ : ∀ p, Ups m ω (η p) = (ω p.1 * y p.2) • x)
    (hηalg : ∀ p i, (η p).1 i ∈ Qbar)
    (V' : Submodule ℂ (Fin 2 → ℂ)) {q : ℕ} (φ : Fin q → Fin m × Fin 2 → ℤ)
    (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ)) (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0)
    (hT : ((V'.prod L₁).map (Ups m ω)) ≤ (ℂ ∙ x)) :
    L₁ = ⊥ ∧ Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin 3 → ℤ => fun j => (s j : ℚ)) ''
          {s : Fin m × Fin 3 → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) = 0 := by
  obtain ⟨hS1, hS2⟩ := DiazModulus.sse_independence_facts m ω hωQ hωalg x y hx hy
  -- an algebraic vector in `T` vanishes
  have halg0 : ∀ (β : ℂ) (v : Fin 2 → ℂ), β ≠ 0 → (∀ i, v i ∈ Qbar) →
      β • v ∈ ℂ ∙ x → β • v = 0 := by
    intro β v hβ hv hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := hS2 β c v hβ hv fun i => by simpa using congrFun hc i
    rw [← hc, this, zero_smul]
  have hTx : ∀ z ∈ V'.prod L₁, Ups m ω z ∈ ℂ ∙ x := fun z hz => hT ⟨z, hz, rfl⟩
  -- no rational kernel
  have hφQ : ∀ v : Fin m × Fin 2 → ℚ, (∀ k, ∑ i, (φ k i : ℚ) * v i = 0) → v = 0 := by
    intro v hv
    set vc : Fin m × Fin 2 → ℂ := fun i => (v i : ℂ) with hvc
    have hvL : vc ∈ L₁ := by
      rw [hL₁]; intro k
      have := congrArg (fun r : ℚ => (r : ℂ)) (hv k)
      simpa [vc] using this
    have hT0 := hTx (0, vc) ⟨V'.zero_mem, hvL⟩
    have halgU : ∀ i, Ups m ω (0, vc) i ∈ Qbar := by
      intro i; rw [Ups_apply]
      exact add_mem (zero_mem _)
        (sum_mem fun k _ => mul_mem (hωalg k) (SubfieldClass.ratCast_mem _ _))
    have h0 := halg0 1 _ one_ne_zero halgU (by rwa [one_smul])
    rw [one_smul] at h0
    funext p
    obtain ⟨a, i⟩ := p
    have hi : ∑ k, ω k * (v (k, i) : ℂ) = 0 := by
      have := congrFun h0 i
      rw [Ups_apply] at this
      simpa [vc] using this
    have hlin := Fintype.linearIndependent_iff.mp hωQ (fun k => v (k, i)) (by
      rw [← hi]; exact Finset.sum_congr rfl fun k _ => by rw [Rat.smul_def, mul_comm])
    simpa using hlin a
  have hL0 : L₁ = ⊥ := by
    rw [eq_bot_iff]; intro v hv
    rw [Submodule.mem_bot]
    exact (DiazModulus.intMatrix_ker_facts φ hφQ).1 v ((hL₁ v).mp hv)
  refine ⟨hL0, ?_⟩
  have hzero : ∀ s : Fin m × Fin 3 → ℤ, (∑ j, (s j : ℂ) • (η j).1) ∈ V' →
      (∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1) → s = 0 := by
    intro s hV hk
    simp only [prod_exp] at hk
    obtain ⟨r, hr⟩ := (DiazModulus.intMatrix_ker_facts φ hφQ).2
      (fun i => ∑ j, (s j : ℂ) * (η j).2 i)
      (fun k => by
        obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hk k)
        exact ⟨n, by rw [hn]; ring⟩)
    have hr' : ∀ i, ∑ j, (s j : ℂ) * (η j).2 i = 2 * (Real.pi : ℂ) * I * r i := hr
    set ζ := ∑ j, (s j : ℂ) • η j with hζ
    have h1 : ζ.1 = ∑ j, (s j : ℂ) • (η j).1 := by simp [hζ, Prod.fst_sum]
    have h2 : ∀ i, ζ.2 i = ∑ j, (s j : ℂ) * (η j).2 i := by
      intro i; simp [hζ, Prod.snd_sum, Finset.sum_apply]
    have hU : Ups m ω ζ = (∑ p, (s p : ℂ) * ω p.1 * y p.2) • x := by
      rw [hζ, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hηΥ, smul_smul, mul_assoc]
    have hζ1alg : ∀ i, ζ.1 i ∈ Qbar := by
      intro i; rw [h1, Finset.sum_apply]
      exact sum_mem fun j _ => by
        simpa using mul_mem (intCast_mem Qbar (s j)) (hηalg j i)
    have hζ10 : ζ.1 = 0 := by
      have := halg0 1 ζ.1 one_ne_zero hζ1alg (by
        rw [one_smul, ← Ups_inl ω ζ.1]; exact hTx _ ⟨h1 ▸ hV, L₁.zero_mem⟩)
      simpa using this
    have hw : Ups m ω ζ = (2 * (Real.pi : ℂ) * I) • fun i => ∑ k, ω k * (r (k, i) : ℂ) := by
      ext i
      rw [Ups_apply, hζ10]
      simp only [Pi.zero_apply, zero_add, h2, hr', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hc := hS2 (2 * (Real.pi : ℂ) * I) (∑ p, (s p : ℂ) * ω p.1 * y p.2) _ Complex.two_pi_I_ne_zero
      (fun i => sum_mem fun k _ => mul_mem (hωalg k) (SubfieldClass.ratCast_mem _ _))
      (fun i => by have := congrFun (hU.symm.trans hw) i; simpa using this)
    exact hS1 s hc
  have hspan : Submodule.span ℚ ((fun s : Fin m × Fin 3 → ℤ => fun j => (s j : ℚ)) ''
      {s : Fin m × Fin 3 → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
        ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1}) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨s, ⟨hV, hk⟩, rfl⟩
    rw [hzero s hV hk]
    funext j; simp
  rw [hspan, finrank_bot]

end C14_S8

open DiazModulus C14_S8 in
theorem solution (m : ℕ) (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (hηΥ : ∀ p, (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) (η p) = (ω p.1 * y p.2) • x)
    (hηalg : ∀ p i, (η p).1 i ∈ Qbar)
    (V' : Submodule ℂ (Fin 2 → ℂ)) {q : ℕ} (φ : Fin q → Fin m × Fin 2 → ℤ)
    (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ)) (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0)
    (hT : ((V'.prod L₁).map (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) ≤ (ℂ ∙ x)) :
    L₁ = ⊥ ∧ Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin 3 → ℤ => fun j => (s j : ℚ)) ''
          {s : Fin m × Fin 3 → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) = 0 := by
  exact main m ω hωQ hωalg x y hx hy η hηΥ hηalg V' φ L₁ hL₁ hT
