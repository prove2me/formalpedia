-- Prove2me | solution 1 for DirectFidelity.State.well_conditioned_m_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:30:35.168669+00:00
-- url     : https://prove2.me/submissions/77c38872-e53f-40f0-9732-1788e61343b5

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

open DirectFidelity.State


theorem solution (n ℓ : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ) (α : ℝ)
    (hα : 0 < α) (hwc : IsWellConditioned ρ α) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hℓ : 0 < ℓ) (k : P n) (hk : chi ρ k ≠ 0) :
    (mDFE ρ ε δ ℓ k : ℝ) ≤ 1 + 2 * Real.log (2 / δ) / (α ^ 2 * (ℓ : ℝ) * ε ^ 2) := by
  have hdim : 0 < dim n := by unfold dim; positivity
  have hchi : dim n * chi ρ k ^ 2 = ((ρ * W k).trace).re ^ 2 := by
    unfold chi; rw [div_pow, Real.sq_sqrt hdim.le]; field_simp
  have hr : ((ρ * W k).trace).re ≠ 0 := by
    intro h; apply hk; unfold chi; rw [h, zero_div]
  have hα2 : α ^ 2 ≤ ((ρ * W k).trace).re ^ 2 := by
    rcases hwc k with h | h
    · exact absurd h hr
    · rw [← sq_abs (((ρ * W k).trace).re)]
      exact pow_le_pow_left₀ hα.le h 2
  have hL : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hr2 : 0 < ((ρ * W k).trace).re ^ 2 := by positivity
  unfold mDFE
  rw [hchi]
  have hx0 : 0 ≤ 2 / (((ρ * W k).trace).re ^ 2 * (ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ) := by positivity
  have h1 := (Nat.ceil_lt_add_one hx0).le
  have h2 : 2 / (((ρ * W k).trace).re ^ 2 * (ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ)
      ≤ 2 * Real.log (2 / δ) / (α ^ 2 * (ℓ : ℝ) * ε ^ 2) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  linarith
