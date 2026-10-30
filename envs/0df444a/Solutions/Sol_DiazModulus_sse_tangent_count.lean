-- Prove2me | solution 1 for DiazModulus.sse_tangent_count
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:12:24.009992+00:00
-- url     : https://prove2.me/submissions/36029a61-4a2c-4a36-b1a2-0bcd58cf4cc4

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The SSE tangent count
`Υ(u, v)_i = u_i + Σ_k ω_k v_{(k,i)}` is surjective onto `ℂ²` (`Υ(u, 0) = u`), so rank–nullity on
`ℂ² × ℂ^{m×2}` gives `dim ker Υ = 2m`. For `P = V' × L₁` and `T = Υ(P)`, rank–nullity for the
restriction of `Υ` to `P` gives `dim V' + dim L₁ = dim T + dim (ker Υ ⊓ P)`; with the hypothesis
`ℓ + dim (ker Υ ⊓ P) = 2m` and the bounds `dim T, dim V' ≤ 2`, `dim L₁ ≤ 2m`, the identity
`ℓ + (2 − dim T) = (2 − dim V') + (2m − dim L₁)` follows by integer arithmetic. Finally
`V' ≤ T`, since `Υ(u, 0) = u` and `(u, 0) ∈ P` for `u ∈ V'`. -/

namespace C14_S6
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

theorem finrank_ker {m : ℕ} (ω : Fin m → ℂ) : Module.finrank ℂ ↥(LinearMap.ker (Ups m ω)) = 2 * m := by
  have hr : LinearMap.range (Ups m ω) = ⊤ :=
    LinearMap.range_eq_top.mpr fun u => ⟨(u, 0), Ups_inl ω u⟩
  have h := LinearMap.finrank_range_add_finrank_ker (Ups m ω)
  rw [hr, finrank_top] at h
  simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_prod] at h
  omega

/-- `↥(p.prod q) ≃ ↥p × ↥q`. -/
def prodEquiv {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (p : Submodule ℂ M) (q : Submodule ℂ N) : ↥(p.prod q) ≃ₗ[ℂ] ↥p × ↥q where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun z := ⟨(z.1.1, z.2.1), ⟨z.1.2, z.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_prod_sub {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [FiniteDimensional ℂ M] [FiniteDimensional ℂ N] (p : Submodule ℂ M) (q : Submodule ℂ N) :
    Module.finrank ℂ ↥(p.prod q) = Module.finrank ℂ ↥p + Module.finrank ℂ ↥q := by
  rw [(prodEquiv p q).finrank_eq, Module.finrank_prod]

theorem rank_nullity {m : ℕ} (ω : Fin m → ℂ) (P : Submodule ℂ ((Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))) :
    Module.finrank ℂ ↥(P.map (Ups m ω)) + Module.finrank ℂ ↥(LinearMap.ker (Ups m ω) ⊓ P)
      = Module.finrank ℂ ↥P := by
  have h := LinearMap.finrank_range_add_finrank_ker ((Ups m ω).domRestrict P)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he : (LinearMap.ker (Ups m ω)).comap P.subtype
      = (LinearMap.ker (Ups m ω) ⊓ P).comap P.subtype := by
    ext z; simp
  rw [he, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at h
  exact h

theorem main {m : ℕ} (ω : Fin m → ℂ) (V' : Submodule ℂ (Fin 2 → ℂ))
    (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ)) (ℓ : ℕ)
    (hℓ : ℓ + Module.finrank ℂ ↥(LinearMap.ker (Ups m ω) ⊓ V'.prod L₁)
      = Module.finrank ℂ ↥(LinearMap.ker (Ups m ω))) :
    Module.finrank ℂ ↥(LinearMap.ker (Ups m ω)) = 2 * m ∧
    ℓ + (2 - Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)))
      = (2 - Module.finrank ℂ ↥V') + (2 * m - Module.finrank ℂ ↥L₁) ∧
    Module.finrank ℂ ↥V' ≤ Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)) := by
  have hk := finrank_ker ω
  have hrn := rank_nullity ω (V'.prod L₁)
  rw [finrank_prod_sub] at hrn
  have hT : Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)) ≤ 2 := by
    have := Submodule.finrank_le ((V'.prod L₁).map (Ups m ω)); simpa using this
  have hV : Module.finrank ℂ ↥V' ≤ 2 := by
    have := Submodule.finrank_le V'; simpa using this
  have hL : Module.finrank ℂ ↥L₁ ≤ 2 * m := by
    have := Submodule.finrank_le L₁
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] at this; omega
  refine ⟨hk, by omega, ?_⟩
  apply Submodule.finrank_mono
  intro u hu
  exact ⟨(u, 0), ⟨hu, L₁.zero_mem⟩, Ups_inl ω u⟩

end C14_S6

open DiazModulus C14_S6 in
theorem solution (m : ℕ) (ω : Fin m → ℂ) (V' : Submodule ℂ (Fin 2 → ℂ)) (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ))
    (ℓ : ℕ) (hℓ : ℓ + Module.finrank ℂ ↥(LinearMap.ker (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) ⊓ V'.prod L₁)
      = Module.finrank ℂ ↥(LinearMap.ker (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)))) :
    Module.finrank ℂ ↥(LinearMap.ker (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) = 2 * m ∧
    ℓ + (2 - Module.finrank ℂ ↥((V'.prod L₁).map (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))))
      = (2 - Module.finrank ℂ ↥V') + (2 * m - Module.finrank ℂ ↥L₁) ∧
    Module.finrank ℂ ↥V' ≤ Module.finrank ℂ ↥((V'.prod L₁).map (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) := by
  exact main ω V' L₁ ℓ hℓ
