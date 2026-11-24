-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux7.budgetTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:56:37.819316+00:00
-- url     : https://prove2.me/submissions/0561102d-3296-493f-8eab-f6fe6181e92f

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetTopConvergence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux7
namespace Formalism.FourierDecayAlt.P.Ux7
theorem _root_.solution : BudgetTop := by
  intro C₁ C₂ Ca
  refine ⟨5 * (C₁ : ℝ) + 9 * Ca + Ca * C₂ + 1, ?_⟩
  intro r n s As al A A₀ hn hs hAs hal hA₀ hA
  set X : ℝ := (r : ℝ) + 1 with hXdef
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hsX : (s : ℝ) ≤ X := by
    have : (s : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast hs
    linarith
  have hrX : (r : ℝ) ≤ X := by linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hAsR : (n : ℝ) ^ 3 ≤ As := by exact_mod_cast hAs
  have hn2 : (n : ℝ) ^ 2 ≤ As := (pow_le_pow_right₀ hn1 (show 2 ≤ 3 by norm_num)).trans hAsR
  have hW1 : (1 : ℝ) ≤ As := (one_le_pow₀ hn1).trans hAsR
  have halR : (al : ℝ) ≤ C₂ * (s : ℝ) ^ 2 + 1 := by exact_mod_cast hal
  have hC₁ : (0 : ℝ) ≤ C₁ := Nat.cast_nonneg _
  have hCa : (0 : ℝ) ≤ Ca := Nat.cast_nonneg _
  have hC₂ : (0 : ℝ) ≤ C₂ := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hal0 : (0 : ℝ) ≤ al := Nat.cast_nonneg _
  have hX4p : (1 : ℝ) ≤ X ^ 4 := one_le_pow₀ hX1
  have hT1 : (1 : ℝ) ≤ X ^ 4 * As := one_le_mul_of_one_le_of_one_le hX4p hW1
  have hX3 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have hX2 : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have hXX : X ≤ X ^ 4 := by simpa using pow_le_pow_right₀ hX1 (show 1 ≤ 4 by norm_num)
  have hX4 : X ^ 4 ≤ X ^ 4 * As := le_mul_of_one_le_right (by positivity) hW1
  have hX3T : X ^ 3 ≤ X ^ 4 * As := hX3.trans hX4
  have hWT : (As : ℝ) ≤ X ^ 4 * As := le_mul_of_one_le_left (by linarith) hX4p
  have hXW : X * As ≤ X ^ 4 * As := mul_le_mul_of_nonneg_right hXX (by linarith)
  have b2 : (Ca : ℝ) * r ^ 2 * (5 * X) ≤ 5 * Ca * (X ^ 4 * As) := by
    have c : (r : ℝ) ^ 2 * X ≤ X ^ 3 :=
      calc (r : ℝ) ^ 2 * X ≤ X ^ 2 * X := by gcongr
        _ = X ^ 3 := by ring
    have c' := mul_le_mul_of_nonneg_left (c.trans hX3T) (show (0 : ℝ) ≤ 5 * Ca by linarith)
    calc (Ca : ℝ) * r ^ 2 * (5 * X) = 5 * Ca * ((r : ℝ) ^ 2 * X) := by ring
      _ ≤ _ := c'
  have b3 : (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ)) ≤ (Ca * (3 + C₂)) * (X ^ 4 * As) := by
    have c1 : (r : ℝ) ^ 3 ≤ X ^ 3 := by gcongr
    have hss : (s : ℝ) ^ 2 ≤ X ^ 2 := by gcongr
    have c2a : (al : ℝ) ≤ C₂ * X ^ 2 + 1 := by linarith [mul_le_mul_of_nonneg_left hss hC₂]
    have c2 : (r : ℝ) * al ≤ X * (C₂ * X ^ 2 + 1) := mul_le_mul hrX c2a hal0 hX0
    have c3 : X * (C₂ * X ^ 2 + 1) = C₂ * X ^ 3 + X := by ring
    have c4 := mul_le_mul_of_nonneg_left hX3T hC₂
    have c5 : X ≤ X ^ 4 * As := hXX.trans hX4
    have : (n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ) ≤ (3 + C₂) * (X ^ 4 * As) := by
      rw [c3] at c2
      linarith
    calc (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ))
        ≤ Ca * ((3 + C₂) * (X ^ 4 * As)) := mul_le_mul_of_nonneg_left this hCa
      _ = _ := by ring
  have b4 : (Ca : ℝ) * r * As ≤ Ca * (X ^ 4 * As) := by
    have := mul_le_mul_of_nonneg_right hrX (show (0 : ℝ) ≤ As by linarith)
    have := mul_le_mul_of_nonneg_left (this.trans hXW) hCa
    linarith
  have b1 : (C₁ : ℝ) * s ^ 3 * (5 * X) ≤ 5 * C₁ * (X ^ 4 * As) := by
    have c : (s : ℝ) ^ 3 * X ≤ X ^ 4 :=
      calc (s : ℝ) ^ 3 * X ≤ X ^ 3 * X := by gcongr
        _ = X ^ 4 := by ring
    have c' := mul_le_mul_of_nonneg_left (c.trans hX4) (show (0 : ℝ) ≤ 5 * C₁ by linarith)
    calc (C₁ : ℝ) * s ^ 3 * (5 * X) = 5 * C₁ * ((s : ℝ) ^ 3 * X) := by ring
      _ ≤ _ := c'
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  linarith
end Formalism.FourierDecayAlt.P.Ux7
