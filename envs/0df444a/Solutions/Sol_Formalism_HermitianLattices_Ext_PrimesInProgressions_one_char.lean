-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.one_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:47:22.017237+00:00
-- url     : https://prove2.me/submissions/b7325d13-961b-4711-bc6e-46d7e5455972

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_mainPsi_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_excW_le_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_excT_sub_le

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
    (Z : Finset ℂ) (m : ℂ → ℕ) (y κ T R : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z)
    (hre : ∀ ρ ∈ Z, 1 / 2 ≤ ρ.re) (hm : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hR : ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ R) :
    ‖psiChi χ y - mainPsi e χ y‖ ≤
      R + 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1)
        + excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have e1 : psiChi χ y - mainPsi e χ y
      = (psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ)
        - ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        + (excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ) := by
    rw [mainPsi_eq]
    have : ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        = ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    rw [this]
    by_cases hχ : χ = 1
    · simp only [if_pos hχ]; ring
    · simp only [if_neg hχ]; ring
  have h2 : ‖∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ‖
      ≤ 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro ρ hρ
    have hw : (0 : ℝ) ≤ (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : ((excW e χ ρ : ℕ) : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast (excW_le_one e χ ρ).trans (hm ρ hρ)
      linarith
    have hn : ‖(m ρ : ℂ) - (excW e χ ρ : ℂ)‖ = (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : (m ρ : ℂ) - (excW e χ ρ : ℂ) = (((m ρ : ℝ) - (excW e χ ρ : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg hw]
    have hρn : 1 / 2 ≤ ‖ρ‖ := (hre ρ hρ).trans ((le_abs_self _).trans (Complex.abs_re_le_norm ρ))
    rw [norm_div, norm_mul, hn, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have h3 : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
      rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
    rw [div_le_iff₀ (by linarith), h3]
    have h4 : 0 ≤ ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * (y * y ^ (ρ.re - 1)) := by positivity
    nlinarith
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hR h2)) ?_)
  exact excT_sub_le hM e he χ Z y κ T hy hT hZ
end Formalism.HermitianLattices.Ext.PrimesInProgressions
