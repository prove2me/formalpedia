-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.abs_psiAP_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:40:30.941439+00:00
-- url     : https://prove2.me/submissions/2f61bf0b-a218-49ee-8d4e-220211fe2064

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_progression_orthogonality


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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (θ β t : ℝ)
    (hmain : ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ)) :
    |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| ≤
      (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / (M.totient : ℝ) := by
  have hφ : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne M))
  have hid := chebyshev_progression_orthogonality M b hb t
  have h1 : (((M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * (psiChi χ t - mainPsi e χ t) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hid, hmain]
    push_cast
    ring
  have h2 : |(M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β)| ≤
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    calc ‖χ ((b : ZMod M)⁻¹)‖ * ‖psiChi χ t - mainPsi e χ t‖ ≤ 1 * ‖psiChi χ t - mainPsi e χ t‖ := by
          gcongr
          exact χ.norm_le_one _
      _ = _ := one_mul _
  rw [le_div_iff₀ hφ]
  have h3 : (psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ) =
      (M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) := by
    unfold Fm
    field_simp
  calc |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| * (M.totient : ℝ)
      = |(psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ)| := by
        rw [abs_mul, abs_of_pos hφ]
    _ ≤ _ := by rw [h3]; exact h2
end Formalism.HermitianLattices.Ext.PrimesInProgressions
