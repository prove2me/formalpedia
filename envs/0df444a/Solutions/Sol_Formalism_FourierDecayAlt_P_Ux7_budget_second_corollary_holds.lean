-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux7.budget_second_corollary_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:39:31.976746+00:00
-- url     : https://prove2.me/submissions/157cda4d-e450-43f5-bcc8-f0f0ae7a5303

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
theorem _root_.solution : DerivativeBudgetCount := by
  intro r m mmB o κjo As Cc A₀ hr hm hmm ho hk hCc hA
  have hX : (m + 1 + mmB) + o ≤ 3 * As := by omega
  refine ⟨hX, ?_⟩
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hXR : ((((m + 1 + mmB) + o : ℕ)) : ℝ) ≤ 3 * As := by exact_mod_cast hX
  have hkR : (κjo : ℝ) ≤ As := by exact_mod_cast hk
  have hmR : (m : ℝ) + 1 ≤ As := by exact_mod_cast hm
  have hmmR : (mmB : ℝ) ≤ As := by exact_mod_cast hmm
  have hAs0 : (0 : ℝ) ≤ As := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have p1 := mul_le_mul_of_nonneg_left hXR (show (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) by linarith)
  have p2 := mul_le_mul_of_nonneg_left hmR (show (0 : ℝ) ≤ 5 * (r : ℝ) by linarith)
  have p3 := mul_le_mul_of_nonneg_left hmmR (show (0 : ℝ) ≤ 2 * (r : ℝ) by linarith)
  have h2 : A₀ - (As : ℝ) - 6 * ((r : ℝ) + 1) * (As : ℝ) ≤
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) := by nlinarith
  have h3' : A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) ≤
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) - 5 * r * ((m : ℝ) + 1) -
        2 * r * mmB := by nlinarith
  have hden : (0 : ℝ) < 8 * (2 * (r : ℝ) + 1) := by linarith
  have ha1 : 8 * (2 * (r : ℝ) + 1) *
      a1 r (A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ)) m mmB =
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) - 5 * r * ((m : ℝ) + 1) -
        2 * r * mmB := by
    unfold a1
    field_simp
  have hrA : (0 : ℝ) ≤ r * As := mul_nonneg hr0 hAs0
  refine ⟨h2, by rw [ha1]; exact h3', by nlinarith, ?_⟩
  apply le_of_mul_le_mul_left _ hden
  rw [ha1]
  have hQ : 0 ≤ (Cc - 20) * (((r : ℝ) + 1) ^ 3 * As) :=
    mul_nonneg (by linarith) (by positivity)
  have h4 : 1 + 4 * (r : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := by
    nlinarith [pow_nonneg hr0 2, pow_nonneg hr0 3, pow_nonneg hr0 4]
  have h5 := mul_le_mul_of_nonneg_right h4 hAs0
  calc 8 * (2 * (r : ℝ) + 1) * ((Cc - 20) / 16 * ((r : ℝ) + 1) ^ 3 * (As : ℝ))
      = (2 * (r : ℝ) + 1) / 2 * ((Cc - 20) * (((r : ℝ) + 1) ^ 3 * As)) := by ring
    _ ≤ ((r : ℝ) + 1) * ((Cc - 20) * (((r : ℝ) + 1) ^ 3 * As)) :=
        mul_le_mul_of_nonneg_right (by linarith) hQ
    _ = Cc * (((r : ℝ) + 1) ^ 4 * As) - 20 * (((r : ℝ) + 1) ^ 4 * As) := by ring
    _ ≤ Cc * (((r : ℝ) + 1) ^ 4 * As) - (13 * (r : ℝ) + 7) * As := by nlinarith
    _ ≤ A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) := by nlinarith
    _ ≤ _ := h3'
end Formalism.FourierDecayAlt.P.Ux7
