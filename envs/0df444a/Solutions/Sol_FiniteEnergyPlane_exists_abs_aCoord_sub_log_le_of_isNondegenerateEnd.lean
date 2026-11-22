-- Prove2me | solution 1 for FiniteEnergyPlane.exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T10:00:36.936005+00:00
-- url     : https://prove2.me/submissions/4a56ce37-8d67-4a7c-8f69-a11d4c7659b7

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib



/-! Hryniewicz Lemma 6.25 helper: logarithmic growth of the `ℝ`-coordinate at a positive end. -/

namespace FiniteEnergyPlane

open Metric
open scoped Real

theorem exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd_aux {n : ℕ} (H : V n → ℝ)
    (P : ReebOrbit H) (u : ℂ → V n) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ d R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      |aCoord H (u z) - P.T * Real.log ‖z‖ / (2 * π) - d| ≤ 1 := by
  obtain ⟨d, -, -, -, h1, -⟩ := huP
  obtain ⟨s₀, hs₀⟩ := h1 1 one_pos
  refine ⟨d, Real.exp (2 * π * s₀), Real.exp_pos _, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact (Real.exp_pos _).not_ge hz
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hs : s₀ ≤ Real.log ‖z‖ / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have := Real.log_le_log (Real.exp_pos _) hz
    rw [Real.log_exp] at this
    linarith
  have hcyl : cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
    unfold cylInf ccwLoop
    rw [mul_div_cancel₀ _ hπ, Real.exp_log hzpos, mul_div_cancel₀ _ hπ]
    exact Complex.norm_mul_exp_arg_mul_I z
  have := hs₀ _ hs (Complex.arg z / (2 * π))
  simp only [endA, hcyl, one_mul, Real.norm_eq_abs] at this
  rwa [mul_div_assoc]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (P : ReebOrbit H) (u : ℂ → V n) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ d R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      |aCoord H (u z) - P.T * Real.log ‖z‖ / (2 * π) - d| ≤ 1 :=
  exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd_aux H P u huP
