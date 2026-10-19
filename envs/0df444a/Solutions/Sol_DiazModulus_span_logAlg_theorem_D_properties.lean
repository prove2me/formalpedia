-- Prove2me | solution 1 for DiazModulus.span_logAlg_theorem_D_properties
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:48:30.631492+00:00
-- url     : https://prove2.me/submissions/787e90cf-c750-49f8-bdb8-dcc216f0090d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_mem_logAlg_adjoin_circle_point_iff
import Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Schanuel_gelfond_schneider
import Theorems.Thm_DiazModulus_six_exponentials
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one
import Theorems.Thm_DiazModulus_logAlg_conj_stable

open Complex ComplexConjugate

/-! # The Theorem D properties of ℒ itself, and Diaz's conjecture as "no candidate in ℒ"

The ℚ-span of `ℒ` is `ℒ` itself: this is `mem_logAlg_adjoin_circle_point_iff` at `u = 0`, where
`c + p·0 + q·conj 0 = c`. So membership in `span ℚ ℒ` means `exp z` algebraic, and every clause is
a classical theorem of the library, applied as stated. Diaz's conjecture, `u ≠ 0 → |u|` algebraic `→ exp u`
transcendental, is then the contrapositive of "no `u ≠ 0` in `span ℚ ℒ` has `|u|` algebraic".
Conjugation is `logAlg_conj_stable`; Baker is `Schanuel.baker_linear_forms_in_logarithms`;
Hermite–Lindemann is `hermite_lindemann_holds`; Gel'fond–Schneider is `Schanuel.gelfond_schneider`,
by contradiction (`β ∉ ℚ` would make `exp (β l₀)` transcendental); the relative Roy clause holds
because `span Q̄ (insert 1 ℒ) ≤ ℒ̃`; six exponentials is `six_exponentials`; and the four exponentials clause is
`four_exponentials_trdeg_one`, verbatim. -/

namespace R19_AXL
open DiazModulus

/-- `span ℚ ℒ = ℒ`, from the membership criterion of `ℒ_u` at `u = 0`. -/
theorem mem_span_logAlg_iff (z : ℂ) : z ∈ Submodule.span ℚ LogAlg ↔ z ∈ LogAlg := by
  constructor
  · intro hz
    obtain ⟨c, hc, p, q, hzc⟩ := ((DiazModulus.mem_logAlg_adjoin_circle_point_iff 0).1 z).1
      (Submodule.mem_sup_left hz)
    rw [hzc]
    simpa using hc
  · exact fun hz => Submodule.subset_span hz

end R19_AXL

open DiazModulus R19_AXL in
theorem solution :
    (DiazModulusConjecture ↔
      ∀ u ∈ Submodule.span ℚ LogAlg, u ≠ 0 → ¬ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) ∧
    /- conjugation -/
    (∀ z ∈ Submodule.span ℚ LogAlg, conj z ∈ Submodule.span ℚ LogAlg) ∧
    /- (D2) Baker -/
    (∀ (n : ℕ) (l : Fin n → ℂ), (∀ i, l i ∈ Submodule.span ℚ LogAlg) → LinearIndependent ℚ l →
      ∀ (b₀ : ℂ) (b : Fin n → ℂ), IsAlgebraic ℚ b₀ → (∀ i, IsAlgebraic ℚ (b i)) →
        (b₀ ≠ 0 ∨ ∃ i, b i ≠ 0) → b₀ + ∑ i, b i * l i ≠ 0) ∧
    /- (D2) Hermite-Lindemann -/
    (∀ z ∈ Submodule.span ℚ LogAlg, IsAlgebraic ℚ z → z = 0) ∧
    /- (D2) Gel'fond-Schneider -/
    (∀ l₀ β : ℂ, l₀ ∈ Submodule.span ℚ LogAlg → β * l₀ ∈ Submodule.span ℚ LogAlg → l₀ ≠ 0 → IsAlgebraic ℚ β →
      ∃ q : ℚ, β = (q : ℂ)) ∧
    /- (D3) Roy, relative to ℒ: strong six exponentials for ℒ̃ gives it for span Q̄ (insert 1 L) -/
    ((∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
        LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
        ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) →
      ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
        LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
        ¬ (∀ i j, x i * y j ∈ Submodule.span Qbar (insert 1 ((Submodule.span ℚ LogAlg : Submodule ℚ ℂ) : Set ℂ)))) ∧
    /- (D3) six exponentials -/
    (∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
      ¬ (∀ i j, x i * y j ∈ Submodule.span ℚ LogAlg)) ∧
    /- (D4) four exponentials in transcendence degree one -/
    (∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ, l₁₁ ∈ Submodule.span ℚ LogAlg → l₁₂ ∈ Submodule.span ℚ LogAlg → l₂₁ ∈ Submodule.span ℚ LogAlg → l₂₂ ∈ Submodule.span ℚ LogAlg →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 → l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧ (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0) ∨
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧ (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0)) := by
  have hS := R19_AXL.mem_span_logAlg_iff
  refine ⟨⟨fun hD u hu hu0 hal => hD u hu0 hal ((hS u).1 hu),
      fun h u hu0 hal hexp => h u ((hS u).2 hexp) hu0 hal⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hS _).2 (logAlg_conj_stable z ((hS z).1 hz))
  · intro n l hl hli b₀ b hb₀ hb hne
    exact Schanuel.baker_linear_forms_in_logarithms n l hli (fun i => (hS _).1 (hl i))
      b₀ b hb₀ hb hne
  · intro z hz halg
    by_contra h0
    exact hermite_lindemann_holds z h0 halg ((hS z).1 hz)
  · intro l₀ β hl hβl hl0 hβ
    by_contra hq
    exact Schanuel.gelfond_schneider β l₀ hβ (fun q h => hq ⟨q, h⟩) ((hS _).1 hl) hl0
      ((hS _).1 hβl)
  · intro hSSE x y hx hy hxy
    have hle : Submodule.span Qbar
        (insert 1 ((Submodule.span ℚ LogAlg : Submodule ℚ ℂ) : Set ℂ)) ≤ LogAlgTilde := by
      refine Submodule.span_le.2 fun w hw => ?_
      rcases hw with rfl | hw
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ ((hS w).1 hw))
    exact hSSE x y hx hy fun i j => hle (hxy i j)
  · intro x y hx hy hxy
    obtain ⟨i, j, hij⟩ := six_exponentials x y hx hy
    exact hij ((hS _).1 (hxy i j))
  · intro l₁₁ l₁₂ l₂₁ l₂₂ h₁₁ h₁₂ h₂₁ h₂₂
    exact four_exponentials_trdeg_one l₁₁ l₁₂ l₂₁ l₂₂
      ((hS _).1 h₁₁) ((hS _).1 h₁₂) ((hS _).1 h₂₁) ((hS _).1 h₂₂)
