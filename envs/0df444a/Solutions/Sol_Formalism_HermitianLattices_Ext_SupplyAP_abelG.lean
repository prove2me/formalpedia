-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.abelG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:47:19.367622+00:00
-- url     : https://prove2.me/submissions/1536873e-d2a5-41ee-8832-f24088b1f280

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffAbel
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_gExp_nonpos
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_neg_half_le_gExp
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_gExp_monotoneOn
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_character_sum_Icc_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ‖∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)‖ ≤ ((q : ℝ) + 1) / 2 := by
  set b : ℕ → ℝ := fun d => gExp ((d : ℝ) / x) with hb
  set S : ℕ → ℂ := fun M => ∑ n ∈ Icc 1 M, χ (n : ZMod q) with hS
  set B : ℝ := (q : ℝ) + 1 with hB
  have hSB : ∀ M, ‖S M‖ ≤ B := fun M => Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ M
  have hB0 : 0 ≤ B := by positivity
  have hpos : ∀ d : ℕ, 1 ≤ d → (0 : ℝ) < (d : ℝ) / x := fun d hd => by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hmono : ∀ d : ℕ, 1 ≤ d → b d ≤ b (d + 1) := by
    intro d hd
    refine gExp_monotoneOn (hpos d hd) (hpos (d + 1) (by omega)) ?_
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hx.le
  have hle0 : ∀ d : ℕ, 1 ≤ d → b d ≤ 0 := fun d hd => gExp_nonpos (hpos d hd)
  have hhalf : -(1 / 2) ≤ b 1 := neg_half_le_gExp (hpos 1 le_rfl)
  set F : ℕ → ℂ := fun N => ∑ d ∈ Icc 1 N, χ (d : ZMod q) * ((b d : ℝ) : ℂ) with hF
  have hT : ∀ M : ℕ, ‖F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ ≤ B * (b (M + 1) - b 1) := by
    intro M
    induction M with
    | zero => simp [hF, hS]
    | succ M ih =>
      have hF1 : F (M + 1 + 1) = F (M + 1) + χ ((M + 1 + 1 : ℕ) : ZMod q) * ((b (M + 1 + 1) : ℝ) : ℂ) := by
        simp only [hF]; rw [Finset.sum_Icc_succ_top (by omega)]
      have hS1 : S (M + 1 + 1) = S (M + 1) + χ ((M + 1 + 1 : ℕ) : ZMod q) := by
        simp only [hS]; rw [Finset.sum_Icc_succ_top (by omega)]
      have heq : F (M + 1 + 1) - S (M + 1 + 1) * ((b (M + 1 + 1) : ℝ) : ℂ) =
          (F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)) - S (M + 1) * ((b (M + 1 + 1) - b (M + 1) : ℝ) : ℂ) := by
        rw [hF1, hS1]; push_cast; ring
      rw [heq]
      have hd := hmono (M + 1) (by omega)
      calc _ ≤ ‖F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ + ‖S (M + 1) * ((b (M + 1 + 1) - b (M + 1) : ℝ) : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ B * (b (M + 1) - b 1) + B * (b (M + 1 + 1) - b (M + 1)) := by
            gcongr
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            exact mul_le_mul_of_nonneg_right (hSB _) (by linarith)
        _ = B * (b (M + 1 + 1) - b 1) := by ring
  change ‖F N‖ ≤ B / 2
  rcases N with _ | M
  · simp [hF]; positivity
  · have h1 := hT M
    have h2 : ‖S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ ≤ B * (-b (M + 1)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hle0 _ (by omega))]
      exact mul_le_mul_of_nonneg_right (hSB _) (by linarith [hle0 (M + 1) (by omega)])
    have h3 : F (M + 1) = (F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)) + S (M + 1) * ((b (M + 1) : ℝ) : ℂ) := by ring
    rw [h3]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ B * (b (M + 1) - b 1) + B * (-b (M + 1)) := add_le_add h1 h2
      _ = B * (-b 1) := by ring
      _ ≤ B / 2 := by nlinarith
end Formalism.HermitianLattices.Ext.SupplyAP
