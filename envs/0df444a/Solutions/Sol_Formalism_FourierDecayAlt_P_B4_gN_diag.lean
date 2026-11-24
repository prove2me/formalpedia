-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.gN_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:40.390565+00:00
-- url     : https://prove2.me/submissions/5c5b1d78-58a0-4bac-aeed-40fd44db980d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (d₁ d₂ : Fin (2 * r + k + 1) → ℂ) (κ : ℝ) (h₁ : ∀ i, ‖d₁ i‖ ≤ κ)
    (h₂ : ∀ i, ‖d₂ i‖ ≤ κ) (g : Mat k r) :
    gN (Matrix.diagonal d₁ * g * Matrix.diagonal d₂) ≤ κ ^ 2 * gN g := by
  unfold gN
  have hκ : 0 ≤ κ := le_trans (norm_nonneg _) (h₁ ⟨0, by omega⟩)
  rw [show κ ^ 2 = Real.sqrt ((κ ^ 2) ^ 2) by rw [Real.sqrt_sq (by positivity)],
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.normSq_mul, Complex.normSq_mul]
  have a1 : Complex.normSq (d₁ i) ≤ κ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (h₁ i) 2
  have a2 : Complex.normSq (d₂ j) ≤ κ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (h₂ j) 2
  have a3 := Complex.normSq_nonneg (g i j)
  have a4 := Complex.normSq_nonneg (d₁ i)
  have a5 := Complex.normSq_nonneg (d₂ j)
  calc Complex.normSq (d₁ i) * Complex.normSq (g i j) * Complex.normSq (d₂ j)
      ≤ κ ^ 2 * Complex.normSq (g i j) * κ ^ 2 := by gcongr
    _ = (κ ^ 2) ^ 2 * Complex.normSq (g i j) := by ring
end Formalism.FourierDecayAlt.P.B4
