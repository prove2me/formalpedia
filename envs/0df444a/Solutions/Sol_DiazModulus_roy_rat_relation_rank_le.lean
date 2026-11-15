-- Prove2me | solution 1 for DiazModulus.roy_rat_relation_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:41:12.966207+00:00
-- url     : https://prove2.me/submissions/bde15599-923b-4141-8f90-22d0a7b4ba39

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The relation rank is at most `dim_ℚ (span_ℚ z ⊓ (T + 2πi·ℚ^d))`
Write `V₀ = span_ℂ(V' ∩ ℚ^d)`, `T = V₀ + L₁` and `ψ(c) = Σ_j c_j z_j` for `c ∈ ℚ^ℓ`; `ψ` is injective
because `z` is ℚ-free. For a relation `s`, put `x_s = Σ_j s_j η_j.1` and `y_s = Σ_j s_j η_j.2`, so that
`ψ(s) = x_s + y_s`. The vector `x_s` lies in `V'` and has rational coordinates, hence lies in `V₀`.
The exponential condition reads `exp(Σ_i φ_{ki} y_{s,i}) = 1`, i.e. `Σ_i φ_{ki} y_{s,i} = 2πi e_k` with
`e_k ∈ ℤ`; applying a ℚ-linear projection `π : ℂ → ℚ` with `π(1) = 1` to `y_s/2πi` gives `r ∈ ℚ^d`
with `Σ_i φ_{ki} r_i = e_k`, so `y_s − 2πi r ∈ L₁`. Hence
`ψ(s) = (x_s + (y_s − 2πi r)) + 2πi r ∈ T + 2πi ℚ^d`, and `ψ(s) ∈ span_ℚ z`. By linearity `ψ` maps the
ℚ-span of the relations into `F = span_ℚ z ⊓ span_ℚ(T + 2πi ℚ^d)`, which is finite-dimensional, and
an injective linear map does not lower the dimension. -/

namespace RC5_RRL
open DiazModulus

theorem prod_exp {N ι : Type*} [Fintype N] [Fintype ι] (a : N → ι → ℂ) (s : N → ℤ) (φ : ι → ℤ) :
    ∏ i, (∏ j, Complex.exp (a j i) ^ s j) ^ φ i
      = Complex.exp (∑ i, (φ i : ℂ) * ∑ j, (s j : ℂ) * a j i) := by
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum]

/-- A ℚ-linear projection `ℂ → ℚ` fixing `ℚ`. -/
theorem exists_ratProj : ∃ π : ℂ →ₗ[ℚ] ℚ, ∀ q : ℚ, π (q : ℂ) = q := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
  exact ⟨g, fun q => by simpa using LinearMap.congr_fun hg q⟩

/-- If `Φ(y) ∈ 2πiℤ^q` for an integer matrix `Φ`, then `y ∈ ker Φ + 2πi ℚ^ι`. -/
theorem rat_lift {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ) (y : ι → ℂ)
    (hy : ∀ k, ∃ e : ℤ, ∑ i, (φ k i : ℂ) * y i = e * (2 * Real.pi * I)) :
    ∃ r : ι → ℚ, ∀ k, ∑ i, (φ k i : ℂ) * (y i - 2 * Real.pi * I * r i) = 0 := by
  obtain ⟨π, hπ⟩ := exists_ratProj
  choose e he using hy
  have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := two_pi_I_ne_zero
  refine ⟨fun i => π (y i / (2 * Real.pi * I)), fun k => ?_⟩
  have hc : ∑ i, (φ k i : ℂ) * (y i / (2 * Real.pi * I)) = ((e k : ℚ) : ℂ) := by
    simp only [← mul_div_assoc, ← Finset.sum_div, he k]
    push_cast; field_simp
  have hsum : ∑ i, (φ k i : ℚ) * π (y i / (2 * Real.pi * I)) = e k := by
    have := congrArg π hc
    rw [hπ, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (φ k i : ℂ) * (y i / (2 * Real.pi * I)) = ((φ k i : ℚ)) • (y i / (2 * Real.pi * I)) by
      rw [Rat.smul_def]; push_cast; rfl, map_smul, smul_eq_mul]
  have hcast := congrArg (fun x : ℚ => (x : ℂ)) hsum
  push_cast at hcast
  calc ∑ i, (φ k i : ℂ) * (y i - 2 * Real.pi * I * (π (y i / (2 * Real.pi * I)) : ℂ))
      = ∑ i, (φ k i : ℂ) * y i
          - 2 * Real.pi * I * ∑ i, (φ k i : ℂ) * (π (y i / (2 * Real.pi * I)) : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hcast, he k]; ring

end RC5_RRL

-- `hη2` is part of the contract but not needed for this bound.
set_option linter.unusedVariables false in
open DiazModulus RC5_RRL in
theorem solution {d ℓ q : ℕ} (z : Fin ℓ → Fin d → ℂ) (hzind : LinearIndependent ℚ z)
    (η : Fin ℓ → (Fin d → ℂ) × (Fin d → ℂ))
    (hη1 : ∀ j i, ∃ r : ℚ, (η j).1 i = (r : ℂ)) (hη2 : ∀ j i, (η j).2 i ∈ LogAlg)
    (hηz : ∀ j, (η j).1 + (η j).2 = z j)
    (V' : Submodule ℂ (Fin d → ℂ)) (φ : Fin q → Fin d → ℤ) (L₁ : Submodule ℂ (Fin d → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin ℓ → ℤ => fun j => (s j : ℚ)) ''
        {s : Fin ℓ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
          ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) ≤
      Module.finrank ℚ ↥(Submodule.span ℚ (Set.range z) ⊓
        Submodule.span ℚ {x : Fin d → ℂ |
          ∃ τ ∈ Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, ∃ r : ℚ, v i = (r : ℂ)} ⊔ L₁,
            ∃ κ : Fin d → ℂ, (∀ i, ∃ r : ℚ, κ i = (r : ℂ)) ∧
              x = τ + (2 * (Real.pi : ℂ) * Complex.I) • κ}) := by
  classical
  set T := Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, ∃ r : ℚ, v i = (r : ℂ)} ⊔ L₁ with hT
  set S := {x : Fin d → ℂ | ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, ∃ r : ℚ, κ i = (r : ℂ)) ∧
    x = τ + (2 * (Real.pi : ℂ) * Complex.I) • κ} with hS
  set F := Submodule.span ℚ (Set.range z) ⊓ Submodule.span ℚ S with hF
  set G := Submodule.span ℚ ((fun s : Fin ℓ → ℤ => fun j => (s j : ℚ)) ''
        {s : Fin ℓ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
          ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1}) with hG
  let ψ : (Fin ℓ → ℚ) →ₗ[ℚ] (Fin d → ℂ) := Fintype.linearCombination ℚ z
  have hψ : ∀ c, ψ c = ∑ j, c j • z j := fun c => Fintype.linearCombination_apply ℚ z c
  choose b hb using hη1
  -- the image of a relation lies in `S`
  have key : ∀ s : Fin ℓ → ℤ, (∑ j, (s j : ℂ) • (η j).1) ∈ V' →
      (∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1) →
      ψ (fun j => (s j : ℚ)) ∈ S := by
    intro s hV hk
    simp only [prod_exp] at hk
    obtain ⟨r, hr⟩ := rat_lift φ (fun i => ∑ j, (s j : ℂ) * (η j).2 i)
      (fun k => Complex.exp_eq_one_iff.mp (hk k))
    refine ⟨(∑ j, (s j : ℂ) • (η j).1) +
        (fun i => (∑ j, (s j : ℂ) * (η j).2 i) - 2 * Real.pi * I * r i),
      Submodule.add_mem_sup ?_ ?_, fun i => (r i : ℂ), fun i => ⟨r i, rfl⟩, ?_⟩
    · refine Submodule.subset_span ⟨hV, fun i => ⟨∑ j, (s j : ℚ) * b j i, ?_⟩⟩
      simp [Finset.sum_apply, hb]
    · rw [hL₁]; exact hr
    · funext i
      simp only [hψ, ← hηz, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Rat.smul_def, Rat.cast_intCast, mul_add, Finset.sum_add_distrib]
      ring
  -- `ψ` maps `G` into `F`
  have hψz : ∀ c, ψ c ∈ Submodule.span ℚ (Set.range z) := by
    intro c; rw [hψ]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hGF : G.map ψ ≤ F := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨s, ⟨hsV, hsexp⟩, rfl⟩
    exact ⟨hψz _, Submodule.subset_span (key s hsV hsexp)⟩
  have : FiniteDimensional ℚ ↥(Submodule.span ℚ (Set.range z)) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range z)
  have hFfin : FiniteDimensional ℚ ↥F := Submodule.finiteDimensional_of_le inf_le_left
  calc Module.finrank ℚ ↥G = Module.finrank ℚ ↥(G.map ψ) :=
        (Submodule.equivMapOfInjective ψ hzind.fintypeLinearCombination_injective G).finrank_eq
    _ ≤ Module.finrank ℚ ↥F := Submodule.finrank_mono hGF
