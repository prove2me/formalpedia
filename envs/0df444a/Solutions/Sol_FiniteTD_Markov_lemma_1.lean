-- Prove2me | solution 1 for FiniteTD.Markov.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:13:07.663857+00:00
-- url     : https://prove2.me/submissions/542ca082-41e5-4913-8478-7b0d6d6a5b2e

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

set_option autoImplicit false
open FiniteTD.Markov
open scoped InnerProductSpace

theorem ftd_dNormSq_smul {S : Type} [Fintype S] {d : ℕ} (π : S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (c : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    dNormSq π φ (c • θ) = c ^ 2 * dNormSq π φ θ := by
  unfold dNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [inner_smul_right]
  ring

theorem solution {S : Type} [Fintype S] {d : ℕ} [NeZero d]
    (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ)
    (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      Real.sqrt ω * ‖θ‖ ≤ Real.sqrt (dNormSq π φ θ) ∧ Real.sqrt (dNormSq π φ θ) ≤ ‖θ‖ := by
  intro θ
  have hn := norm_nonneg θ
  constructor
  · rcases eq_or_ne θ 0 with h0 | h0
    · simp [h0]
    · have hpos : 0 < ‖θ‖ := norm_pos_iff.mpr h0
      have hu : ‖(‖θ‖⁻¹) • θ‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      have h1 : ω ≤ dNormSq π φ ((‖θ‖⁻¹) • θ) := hω.2 ⟨_, hu, rfl⟩
      rw [ftd_dNormSq_smul] at h1
      have h2 : ω * ‖θ‖ ^ 2 ≤ dNormSq π φ θ := by
        have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖θ‖)
        have e : ‖θ‖⁻¹ ^ 2 * dNormSq π φ θ * ‖θ‖ ^ 2 = dNormSq π φ θ := by
          field_simp
        linarith
      calc Real.sqrt ω * ‖θ‖ = Real.sqrt (ω * ‖θ‖ ^ 2) := by
            rw [Real.sqrt_mul hω0.le, Real.sqrt_sq hn]
        _ ≤ Real.sqrt (dNormSq π φ θ) := Real.sqrt_le_sqrt h2
  · rw [Real.sqrt_le_iff]
    refine ⟨hn, ?_⟩
    unfold dNormSq
    calc ∑ s, π s * ⟪φ s, θ⟫_ℝ ^ 2 ≤ ∑ s, π s * ‖θ‖ ^ 2 := by
          refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hπ0 s)
          have h := abs_real_inner_le_norm (φ s) θ
          have h' : |⟪φ s, θ⟫_ℝ| ≤ ‖θ‖ :=
            h.trans (by nlinarith [hφ s, norm_nonneg (φ s)])
          have := sq_abs ⟪φ s, θ⟫_ℝ
          nlinarith [abs_nonneg ⟪φ s, θ⟫_ℝ]
      _ = ‖θ‖ ^ 2 := by rw [← Finset.sum_mul, hπ1, one_mul]
