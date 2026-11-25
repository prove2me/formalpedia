-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.excT_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:01.34902+00:00
-- url     : https://prove2.me/submissions/7b1a44bf-d231-4b42-8a72-05ad98f57e09

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmB

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
theorem _root_.solution {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y κ T : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) :
    ‖excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI, excT]
  · obtain ⟨-, hne, hz, hlo, hhi⟩ := he _ rfl
    simp only at hne hz hlo hhi
    simp only [excW, excI, excT]
    by_cases h : χ = χ₁
    · subst h
      simp only [true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℂ)) * (y : ℂ) ^ ρ / ρ
          = if ρ = (β₁ : ℂ) then (y : ℂ) ^ ρ / ρ else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      have hy0 : 0 < y := by linarith
      split_ifs with hm
      · simp only [sub_self, norm_zero, one_mul]; positivity
      · have hb : β₁ < 1 - κ / 2 := by
          by_contra hcon
          push Not at hcon
          exact hm (hZ _ ⟨Or.inl hne, hz⟩ (by simpa using hcon) (by simpa using hT))
        have hl : 1 ≤ Real.log M := by
          rw [Real.le_log_iff_exp_le (by positivity)]
          have : (3 : ℝ) ≤ M := by exact_mod_cast hM
          linarith [Real.exp_one_lt_d9]
        have hb2 : 1 / 2 ≤ β₁ := by
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num); linarith
          linarith
        rw [sub_zero, one_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have h1 : y ^ β₁ ≤ y ^ (1 - κ / 2) := Real.rpow_le_rpow_of_exponent_le hy hb.le
        have h2 : y ^ (1 - κ / 2) = y * y ^ (-(κ / 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_one]
        rw [div_le_iff₀ (by linarith)]
        have h3 : 0 ≤ y * y ^ (-(κ / 2)) := by positivity
        nlinarith
    · simp [h]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
