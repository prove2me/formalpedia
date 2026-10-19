-- Prove2me | solution 1 for DiazModulus.logAlg_adjoin_circle_point_theorem_D
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:50:37.734337+00:00
-- url     : https://prove2.me/submissions/d7dcb1ea-bab5-46ad-ae39-1f8f4e182180

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_mem_logAlg_adjoin_circle_point_iff
import Theorems.Thm_DiazModulus_logAlg_adjoin_circle_point_baker_linear_forms
import Theorems.Thm_DiazModulus_logAlg_adjoin_circle_point_hermite_lindemann_gelfond_schneider
import Theorems.Thm_DiazModulus_logAlg_adjoin_circle_point_six_exponentials
import Theorems.Thm_DiazModulus_logAlg_adjoin_circle_point_four_exponentials_trdeg_one
import Theorems.Thm_DiazModulus_logAlgTilde_adjoin_circle_point_no_two_by_three_configuration
import Theorems.Thm_DiazModulus_logAlg_conj_stable

open Complex ComplexConjugate

/-! # Theorem D: ℒ_u = ℒ + ℚu + ℚū at a generic circle point

Let `u` be transcendental over `F = ℚ(ℒ̃)` with `u ū` algebraic, and `ℒ_u = span ℚ ℒ ⊔ span ℚ {u, ū}`.
(D1): `ℒ ⊆ ℒ_u` and `u ∈ ℒ_u` by `le_sup_left`/`le_sup_right`; `u ∉ Q̄` because `Q̄ ⊆ ℒ̃ ⊆ F` and `u`
is not algebraic over `F` (so also `u ≠ 0`); `|u|` is algebraic because `|u|² = u ū`
(`Complex.mul_conj'`, `IsAlgebraic.of_pow`). Conjugation: by the membership criterion of
`mem_logAlg_adjoin_circle_point_iff`, `conj (c + pu + qū) = c̄ + qu + pū` with `c̄ ∈ ℒ` by
`logAlg_conj_stable`. Baker, Hermite–Lindemann and Gel'fond–Schneider for `ℒ_u` are
`logAlg_adjoin_circle_point_baker_linear_forms` and `logAlg_adjoin_circle_point_hermite_lindemann_gelfond_schneider`. The relative Roy clause: the second half of the same criterion rewrites
`span Q̄ (insert 1 ℒ_u)` as `ℒ̃ ⊔ span Q̄ {u, ū}`, which is the space of
`logAlgTilde_adjoin_circle_point_no_two_by_three_configuration`, so that result applies. Six exponentials and the four
exponentials clause are `logAlg_adjoin_circle_point_six_exponentials` and
`logAlg_adjoin_circle_point_four_exponentials_trdeg_one`. -/

namespace R19_TD
open DiazModulus

/-- `|u|` is algebraic when `u ū` is. -/
theorem isAlgebraic_norm (u : ℂ) (hρ : IsAlgebraic ℚ (u * conj u)) :
    IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) := by
  rw [Complex.mul_conj'] at hρ
  exact IsAlgebraic.of_pow two_pos hρ

/-- A point transcendental over `ℚ(ℒ̃)` is not algebraic, since `Q̄ ⊆ ℒ̃`. -/
theorem not_mem_Qbar (u : ℂ) (hu : Transcendental (Subfield.closure (LogAlgTilde : Set ℂ)) u) :
    u ∉ Qbar := by
  intro hq
  have h1 : u ∈ LogAlgTilde := by
    have h := Submodule.smul_mem LogAlgTilde (⟨u, hq⟩ : Qbar)
      (Submodule.subset_span (Set.mem_insert (1 : ℂ) LogAlg))
    rwa [show (⟨u, hq⟩ : Qbar) • (1 : ℂ) = u from mul_one u] at h
  exact hu (isAlgebraic_algebraMap
    (⟨u, Subfield.subset_closure h1⟩ : Subfield.closure (LogAlgTilde : Set ℂ)))

end R19_TD

open DiazModulus R19_TD in
theorem solution
    (u : ℂ) (hρ : IsAlgebraic ℚ (u * conj u))
    (hu : Transcendental (Subfield.closure (LogAlgTilde : Set ℂ)) u) :
    (∀ z ∈ LogAlg, z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ))) ∧
    u ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) ∧ u ∉ Qbar ∧ u ≠ 0 ∧ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) ∧
    /- conjugation -/
    (∀ z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)), conj z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ))) ∧
    /- (D2) Baker -/
    (∀ (n : ℕ) (l : Fin n → ℂ), (∀ i, l i ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ))) → LinearIndependent ℚ l →
      ∀ (b₀ : ℂ) (b : Fin n → ℂ), IsAlgebraic ℚ b₀ → (∀ i, IsAlgebraic ℚ (b i)) →
        (b₀ ≠ 0 ∨ ∃ i, b i ≠ 0) → b₀ + ∑ i, b i * l i ≠ 0) ∧
    /- (D2) Hermite-Lindemann -/
    (∀ z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)), IsAlgebraic ℚ z → z = 0) ∧
    /- (D2) Gel'fond-Schneider -/
    (∀ l₀ β : ℂ, l₀ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) → β * l₀ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) → l₀ ≠ 0 → IsAlgebraic ℚ β →
      ∃ q : ℚ, β = (q : ℂ)) ∧
    /- (D3) Roy, relative to ℒ: strong six exponentials for ℒ̃ gives it for span Q̄ (insert 1 L) -/
    ((∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
        LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
        ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) →
      ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
        LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
        ¬ (∀ i j, x i * y j ∈ Submodule.span Qbar (insert 1 ((Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ) : Submodule ℚ ℂ) : Set ℂ)))) ∧
    /- (D3) six exponentials -/
    (∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
      ¬ (∀ i j, x i * y j ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)))) ∧
    /- (D4) four exponentials in transcendence degree one -/
    (∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ, l₁₁ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) → l₁₂ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) → l₂₁ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) → l₂₂ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 → l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧ (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0) ∨
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧ (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0)) := by
  have hM := DiazModulus.mem_logAlg_adjoin_circle_point_iff u
  have hB3 := DiazModulus.logAlg_adjoin_circle_point_hermite_lindemann_gelfond_schneider u hρ hu
  have huQ := R19_TD.not_mem_Qbar u hu
  refine ⟨fun z hz => Submodule.mem_sup_left (Submodule.subset_span hz),
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _)), huQ,
    fun h => huQ (h ▸ Qbar.zero_mem), R19_TD.isAlgebraic_norm u hρ, ?_, ?_, hB3.1, hB3.2,
    ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, hc, p, q, rfl⟩ := (hM.1 z).1 hz
    refine (hM.1 _).2 ⟨conj c, logAlg_conj_stable c hc, q, p, ?_⟩
    simp only [map_add, map_mul, map_ratCast, Complex.conj_conj]
    ring
  · intro n l hl hli b₀ b hb₀ hb hne
    exact DiazModulus.logAlg_adjoin_circle_point_baker_linear_forms u hρ hu n l hli hl
      b₀ b hb₀ hb hne
  · intro hSSE x y hx hy hxy
    rw [hM.2] at hxy
    exact DiazModulus.logAlgTilde_adjoin_circle_point_no_two_by_three_configuration hSSE u hρ hu
      ⟨x, y, hx, hy, hxy⟩
  · intro x y hx hy hxy
    exact DiazModulus.logAlg_adjoin_circle_point_six_exponentials u hρ hu ⟨x, y, hx, hy, hxy⟩
  · intro l₁₁ l₁₂ l₂₁ l₂₂ h₁₁ h₁₂ h₂₁ h₂₂ n₁₁ n₁₂ n₂₁ n₂₂ hdet htr
    exact DiazModulus.logAlg_adjoin_circle_point_four_exponentials_trdeg_one u hρ hu
      l₁₁ l₁₂ l₂₁ l₂₂ h₁₁ h₁₂ h₂₁ h₂₂ n₁₁ n₁₂ n₂₁ n₂₂ hdet htr
