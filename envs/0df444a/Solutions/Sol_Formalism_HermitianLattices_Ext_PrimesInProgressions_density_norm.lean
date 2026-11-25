-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.density_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:33:27.823407+00:00
-- url     : https://prove2.me/submissions/63287413-4502-48d9-b854-4b1668306e34

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSumB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (h : LogDensityM) :
    ∃ a B C : ℝ, 1 ≤ a ∧ 0 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℕ) [NeZero M] (T v : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 3 ≤ M → 2 ≤ T →
      (∀ p ∈ S, 1 / 2 ≤ p.2.re ∧ p.2.re ≤ 1 ∧ Real.log ((M : ℝ) * T) * (1 - p.2.re) ≤ v ∧ |p.2.im| ≤ T ∧
        IsLZero p.1 p.2) →
      (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
      (S.card : ℝ) ≤ C * Real.exp (a * v) * Real.log ((M : ℝ) * T) ^ B := by
  obtain ⟨A, B, C, h⟩ := h
  refine ⟨max A 1, max B 0, max C 1, le_max_right _ _, le_max_right _ _, le_max_right _ _, ?_⟩
  intro M _ T v S hM hT hS hsp
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMT : (6 : ℝ) ≤ (M : ℝ) * T := by nlinarith
  set ℓ : ℝ := Real.log ((M : ℝ) * T) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  rcases S.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp only [card_empty, Nat.cast_zero]
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  have hv : 0 ≤ v := by
    obtain ⟨_, h2, h3, _⟩ := hS p0 hp0
    have : 0 ≤ ℓ * (1 - p0.2.re) := mul_nonneg hℓ0.le (by linarith)
    linarith
  set σ : ℝ := max (1 / 2) (1 - v / ℓ) with hσ
  have hσ1 : σ ≤ 1 := by
    apply max_le (by norm_num)
    have : 0 ≤ v / ℓ := div_nonneg hv hℓ0.le
    linarith
  have hσ2 : 1 - σ ≤ v / ℓ := by
    have := le_max_right (1 / 2 : ℝ) (1 - v / ℓ)
    linarith
  have key := h M T σ S hM hT (le_max_left _ _) (by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
    refine ⟨max_le h1 ?_, h4, h5⟩
    have : 1 - p.2.re ≤ v / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
    linarith) hsp
  refine key.trans ?_
  have e1 : ((M : ℝ) * T) ^ (A * (1 - σ)) ≤ Real.exp (max A 1 * v) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have h1 : A * (1 - σ) ≤ max A 1 * (v / ℓ) := by
      have hA0 : 0 ≤ max A 1 := le_trans zero_le_one (le_max_right _ _)
      calc A * (1 - σ) ≤ max A 1 * (1 - σ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ max A 1 * (v / ℓ) := mul_le_mul_of_nonneg_left hσ2 hA0
    calc ℓ * (A * (1 - σ)) ≤ ℓ * (max A 1 * (v / ℓ)) := mul_le_mul_of_nonneg_left h1 hℓ0.le
      _ = max A 1 * v := by field_simp
  have e2 : ℓ ^ B ≤ ℓ ^ (max B 0) := Real.rpow_le_rpow_of_exponent_le hℓ1 (le_max_left _ _)
  have p1 : 0 ≤ ((M : ℝ) * T) ^ (A * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  have p2 : 0 ≤ ℓ ^ B := Real.rpow_nonneg hℓ0.le _
  have hC0 : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
  calc C * ((M : ℝ) * T) ^ (A * (1 - σ)) * ℓ ^ B
      ≤ max C 1 * ((M : ℝ) * T) ^ (A * (1 - σ)) * ℓ ^ B := by
        apply mul_le_mul_of_nonneg_right _ p2
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) p1
    _ ≤ max C 1 * Real.exp (max A 1 * v) * ℓ ^ (max B 0) := by
        apply mul_le_mul _ e2 p2 (by positivity)
        exact mul_le_mul_of_nonneg_left e1 hC0
end Formalism.HermitianLattices.Ext.PrimesInProgressions
