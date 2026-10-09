-- Prove2me | solution 1 for DiazModulus.candidate_sum_div_sq_sub_not_mem_logAlgTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T09:02:11.399888+00:00
-- url     : https://prove2.me/submissions/8a99840e-3cb3-424c-b6f7-6007f91c0fa5

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_candidate_two_pole_not_both_mem_logAlgTilde
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable

open Complex ComplexConjugate

/-!
# `u/(u² − a₁) + u/(u² − a₂)` at a candidate, when `aᵢ āᵢ = (u ū)²`

Under Roy's strong six exponentials theorem, let `u` be a candidate, `ρ = u ū`, and `a₁ ≠ a₂`
non-zero algebraic numbers with `aᵢ āᵢ = ρ²`. Then `z₁ + z₂ ∉ ℒ̃`, where `zᵢ = u/(u² − aᵢ)`.

Since `ū = ρ/u` and `ρ²/āᵢ = aᵢ`, conjugation acts on each `zᵢ` by a scalar:
`z̄ᵢ = -(ρ/āᵢ) zᵢ` (`conj_pole`; when `u² = aᵢ` both sides are `0`). Put `kᵢ = -(ρ/āᵢ) ∈ Q̄`.
If `z = z₁ + z₂ ∈ ℒ̃`, then `z̄ = k₁ z₁ + k₂ z₂ ∈ ℒ̃` (`logAlgTilde_conj_stable`). As `ρ ≠ 0`
and `ā₁ ≠ ā₂`, `k₁ ≠ k₂`, so `z₁ = (k₁ − k₂)⁻¹ (z̄ − k₂ z)` and `z₂ = z − z₁` lie in the
`Q̄`-space `ℒ̃`, against `candidate_two_pole_not_both_mem_logAlgTilde`.
-/

namespace R7_twoPoleSum

open DiazModulus

/-- `Q̄` is stable under complex conjugation. -/
theorem conj_mem_Qbar {c : ℂ} (hc : c ∈ Qbar) : conj c ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 hc).algHom
    ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ))

theorem smul_mem' {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ LogAlgTilde) : c * v ∈ LogAlgTilde := by
  have := LogAlgTilde.smul_mem (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- With `a ā = (u ū)²`, conjugation multiplies `u/(u² − a)` by `-(u ū)/ā`. -/
theorem conj_pole {u a : ℂ} (ha0 : a ≠ 0) (h : a * conj a = (u * conj u) ^ 2) :
    conj (u / (u ^ 2 - a)) = -(u * conj u / conj a) * (u / (u ^ 2 - a)) := by
  by_cases hd : u ^ 2 - a = 0
  · rw [hd, div_zero, map_zero, mul_zero]
  have hcd : conj u ^ 2 - conj a ≠ 0 := by
    rw [← map_pow, ← map_sub]; exact (_root_.map_ne_zero _).2 hd
  have hā0 : conj a ≠ 0 := (_root_.map_ne_zero _).2 ha0
  rw [map_div₀, map_sub, map_pow]
  field_simp
  linear_combination (-conj u) * h

end R7_twoPoleSum

open DiazModulus R7_twoPoleSum in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) {a₁ a₂ : ℂ} (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar)
    (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha : a₁ ≠ a₂)
    (h₁ : a₁ * conj a₁ = (u * conj u) ^ 2) (h₂ : a₂ * conj a₂ = (u * conj u) ^ 2) :
    u / (u ^ 2 - a₁) + u / (u ^ 2 - a₂) ∉ LogAlgTilde := by
  intro hz
  have hu0 : u ≠ 0 := h.1
  have hρ : u * conj u ∈ Qbar := by
    rw [Complex.mul_conj']
    exact Qbar.pow_mem (mem_Qbar_iff.2 h.2.1) 2
  have hρ0 : u * conj u ≠ 0 := mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0)
  have hā₁0 : conj a₁ ≠ 0 := (_root_.map_ne_zero _).2 ha₁0
  have hā₂0 : conj a₂ ≠ 0 := (_root_.map_ne_zero _).2 ha₂0
  have hā : conj a₁ ≠ conj a₂ := fun e => ha ((RingHom.injective _) e)
  set z₁ := u / (u ^ 2 - a₁) with hz₁
  set z₂ := u / (u ^ 2 - a₂) with hz₂
  set k₁ := -(u * conj u / conj a₁) with hk₁
  set k₂ := -(u * conj u / conj a₂) with hk₂
  have hk₁Q : k₁ ∈ Qbar := neg_mem (div_mem hρ (conj_mem_Qbar ha₁))
  have hk₂Q : k₂ ∈ Qbar := neg_mem (div_mem hρ (conj_mem_Qbar ha₂))
  have hk : k₁ - k₂ ≠ 0 := by
    rw [hk₁, hk₂]
    intro e
    apply hā
    field_simp at e
    exact (mul_left_cancel₀ hρ0 (by linear_combination -e)).symm
  have hc : conj (z₁ + z₂) = k₁ * z₁ + k₂ * z₂ := by
    rw [map_add, hz₁, hz₂, conj_pole ha₁0 h₁, conj_pole ha₂0 h₂]
  have hzc : k₁ * z₁ + k₂ * z₂ ∈ LogAlgTilde := hc ▸ logAlgTilde_conj_stable _ hz
  have hm₁ : z₁ ∈ LogAlgTilde := by
    have := smul_mem' (inv_mem (sub_mem hk₁Q hk₂Q))
      (LogAlgTilde.sub_mem hzc (smul_mem' hk₂Q hz))
    convert this using 1
    field_simp
    ring
  have hm₂ : z₂ ∈ LogAlgTilde := by
    convert LogAlgTilde.sub_mem hz hm₁ using 1
    ring
  exact candidate_two_pole_not_both_mem_logAlgTilde hSSE h ha₁ ha₂ ha₁0 ha₂0 ha ⟨hm₁, hm₂⟩
