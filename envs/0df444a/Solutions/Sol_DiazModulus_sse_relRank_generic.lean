-- Prove2me | solution 1 for DiazModulus.sse_relRank_generic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:12:13.216016+00:00
-- url     : https://prove2.me/submissions/7bcb44d6-8185-4abb-a574-cc872ba1daa0

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_sse_independence_facts
import Theorems.Thm_DiazModulus_rank_le_of_injOn_lattice

open Complex ComplexConjugate

/-! # The relation rank in the generic case `T ∩ ℂx = 0`
Write `Υ(u, v)_i = u_i + Σ_k ω_k v_{(k,i)}`, `T = Υ(V' × L₁)` and `a_{ji} = exp((η_j).2_i)`. The
multiplicative condition `Π_i (Π_j a_{ji}^{s_j})^{φ_{ki}} = 1` equals `exp(Ψ(s)_k) = 1` for the
ℂ-linear map `Ψ(z)_k = Σ_i φ_{ki} Σ_j z_j (η_j).2_i` (`Complex.exp_int_mul`, `Complex.exp_sum`),
so the relation set is an additive subgroup `A ≤ ℤ^{m×3}` with `Ψ(A) ⊆ 2πiℤ^q`
(`Complex.exp_eq_one_iff`). `Ψ` is injective on `A`: if `Ψ(s) = 0` then `ζ = Σ_j s_j η_j` lies in
`V' × L₁`, and `Υ(ζ) = (Σ_j s_j ω_{j.1} y_{j.2}) x` lies in `T ∩ ℂx = 0`; as `x ≠ 0`, the
coefficient vanishes and `s = 0` by `sse_independence_facts`. Then `rank_le_of_injOn_lattice`
bounds the rank by `dim range Ψ ≤ dim range Φ = 2m − dim L₁`, where `Φ(v)_k = Σ_i φ_{ki} v_i` has
kernel `L₁` (rank–nullity). -/

namespace C14_S7
open DiazModulus

noncomputable def Ups (m : ℕ) (ω : Fin m → ℂ) :
    ((Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi fun i : Fin 2 =>
    (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
    + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)

theorem prod_exp {N ι : Type*} [Fintype N] [Fintype ι] (a : N → ι → ℂ) (s : N → ℤ) (φ : ι → ℤ) :
    ∏ i, (∏ j, Complex.exp (a j i) ^ s j) ^ φ i
      = Complex.exp (∑ i, (φ i : ℂ) * ∑ j, (s j : ℂ) * a j i) := by
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum]

variable {m : ℕ} {q : ℕ}

/-- `Φ(v)_k = Σ_i φ_{ki} v_i`. -/
noncomputable def Phi (φ : Fin q → Fin m × Fin 2 → ℤ) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] (Fin q → ℂ) where
  toFun v k := ∑ i, (φ k i : ℂ) * v i
  map_add' v w := by ext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext k; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

/-- `Ψ(z) = Φ(Σ_j z_j (η_j).2)`. -/
noncomputable def Psi (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (φ : Fin q → Fin m × Fin 2 → ℤ) : (Fin m × Fin 3 → ℂ) →ₗ[ℂ] (Fin q → ℂ) where
  toFun z k := ∑ i, (φ k i : ℂ) * ∑ j, z j * (η j).2 i
  map_add' z w := by ext k; simp [add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    ext k; simp [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem Psi_eq (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (φ : Fin q → Fin m × Fin 2 → ℤ) (z : Fin m × Fin 3 → ℂ) :
    Psi η φ z = Phi φ (fun i => ∑ j, z j * (η j).2 i) := rfl

/-- The relation set, verbatim. -/
def Sset (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) (V' : Submodule ℂ (Fin 2 → ℂ))
    (φ : Fin q → Fin m × Fin 2 → ℤ) : Set (Fin m × Fin 3 → ℤ) :=
  {s | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
    ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1}

theorem mem_Sset {η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)} {V' : Submodule ℂ (Fin 2 → ℂ)}
    {φ : Fin q → Fin m × Fin 2 → ℤ} {s : Fin m × Fin 3 → ℤ} :
    s ∈ Sset η V' φ ↔ (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
      ∀ k, Complex.exp (Psi η φ (fun j => (s j : ℂ)) k) = 1 := by
  simp only [Sset, Set.mem_ofPred_eq, prod_exp]; rfl

/-- The relation set as an additive subgroup. -/
def Agrp (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) (V' : Submodule ℂ (Fin 2 → ℂ))
    (φ : Fin q → Fin m × Fin 2 → ℤ) : AddSubgroup (Fin m × Fin 3 → ℤ) where
  carrier := Sset η V' φ
  zero_mem' := by
    rw [mem_Sset]
    refine ⟨by simp, fun k => ?_⟩
    have : (fun j => (((0 : Fin m × Fin 3 → ℤ) j : ℤ) : ℂ)) = 0 := by ext; simp
    rw [this, map_zero]; simp
  add_mem' := by
    intro s t hs ht
    rw [mem_Sset] at *
    refine ⟨?_, fun k => ?_⟩
    · have : ∑ j, (((s + t) j : ℤ) : ℂ) • (η j).1
          = ∑ j, (s j : ℂ) • (η j).1 + ∑ j, (t j : ℂ) • (η j).1 := by
        simp [add_smul, Finset.sum_add_distrib]
      rw [this]; exact V'.add_mem hs.1 ht.1
    · have hc : (fun j => (((s + t) j : ℤ) : ℂ)) = (fun j => (s j : ℂ)) + fun j => (t j : ℂ) := by
        ext; simp
      rw [hc, map_add, Pi.add_apply, Complex.exp_add, hs.2 k, ht.2 k, mul_one]
  neg_mem' := by
    intro s hs
    rw [mem_Sset] at *
    refine ⟨?_, fun k => ?_⟩
    · have : ∑ j, (((-s) j : ℤ) : ℂ) • (η j).1 = -∑ j, (s j : ℂ) • (η j).1 := by
        simp [Finset.sum_neg_distrib]
      rw [this]; exact V'.neg_mem hs.1
    · have hc : (fun j => (((-s) j : ℤ) : ℂ)) = -fun j => (s j : ℂ) := by ext; simp
      rw [hc, map_neg, Pi.neg_apply, Complex.exp_neg, hs.2 k, inv_one]

theorem ker_Phi (φ : Fin q → Fin m × Fin 2 → ℤ) (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) : LinearMap.ker (Phi φ) = L₁ := by
  ext v
  rw [LinearMap.mem_ker, hL₁, funext_iff]
  rfl

theorem finrank_range_Psi (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (φ : Fin q → Fin m × Fin 2 → ℤ) (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) :
    Module.finrank ℂ ↥(LinearMap.range (Psi η φ)) ≤ 2 * m - Module.finrank ℂ ↥L₁ := by
  have hle : LinearMap.range (Psi η φ) ≤ LinearMap.range (Phi φ) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨_, (Psi_eq η φ z).symm⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker (Phi φ)
  rw [ker_Phi φ L₁ hL₁] at h2
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] at h2
  omega

theorem main (m : ℕ) (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (hηΥ : ∀ p, Ups m ω (η p) = (ω p.1 * y p.2) • x)
    (V' : Submodule ℂ (Fin 2 → ℂ)) {q : ℕ} (φ : Fin q → Fin m × Fin 2 → ℤ)
    (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ)) (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0)
    (hT : ((V'.prod L₁).map (Ups m ω)) ⊓ (ℂ ∙ x) = ⊥) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin 3 → ℤ => fun j => (s j : ℚ)) ''
          (Agrp η V' φ : Set (Fin m × Fin 3 → ℤ))))
      ≤ 2 * m - Module.finrank ℂ ↥L₁ := by
  have hS2 := (DiazModulus.sse_independence_facts m ω hωQ hωalg x y hx hy).1
  have hx0 : x ≠ 0 := by
    intro h; exact hx.ne_zero 0 (by simp [h])
  refine le_trans (DiazModulus.rank_le_of_injOn_lattice (Psi η φ) (Agrp η V' φ) ?_ ?_)
    (finrank_range_Psi η φ L₁ hL₁)
  · intro s hs
    have hs' := (mem_Sset.mp hs).2
    choose e he using fun k => Complex.exp_eq_one_iff.mp (hs' k)
    exact ⟨e, funext fun k => by rw [he k]; ring⟩
  · intro s hs h0
    have hs' := mem_Sset.mp hs
    set ζ := ∑ j, (s j : ℂ) • η j with hζ
    have h1 : ζ.1 = ∑ j, (s j : ℂ) • (η j).1 := by simp [hζ, Prod.fst_sum]
    have h2 : ζ.2 = fun i => ∑ j, (s j : ℂ) * (η j).2 i := by
      ext i; simp [hζ, Prod.snd_sum, Finset.sum_apply]
    have hmem : ζ ∈ V'.prod L₁ := by
      refine ⟨h1 ▸ hs'.1, ?_⟩
      show ζ.2 ∈ L₁
      rw [hL₁, h2]
      intro k
      exact congrFun h0 k
    have hU : Ups m ω ζ = (∑ p, (s p : ℂ) * ω p.1 * y p.2) • x := by
      rw [hζ, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hηΥ, smul_smul, mul_assoc]
    have hin : Ups m ω ζ ∈ ((V'.prod L₁).map (Ups m ω)) ⊓ (ℂ ∙ x) :=
      ⟨⟨ζ, hmem, rfl⟩, hU ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)⟩
    rw [hT, Submodule.mem_bot, hU, smul_eq_zero] at hin
    exact hS2 s (hin.resolve_right hx0)

end C14_S7

open DiazModulus C14_S7 in
theorem solution (m : ℕ) (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (hηΥ : ∀ p, (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) (η p) = (ω p.1 * y p.2) • x)
    (V' : Submodule ℂ (Fin 2 → ℂ)) {q : ℕ} (φ : Fin q → Fin m × Fin 2 → ℤ)
    (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ)) (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0)
    (hT : ((V'.prod L₁).map (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) ⊓ (ℂ ∙ x) = ⊥) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin 3 → ℤ => fun j => (s j : ℚ)) ''
          {s : Fin m × Fin 3 → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1}))
      ≤ 2 * m - Module.finrank ℂ ↥L₁ := by
  exact main m ω hωQ hωalg x y hx hy η hηΥ V' φ L₁ hL₁ hT
