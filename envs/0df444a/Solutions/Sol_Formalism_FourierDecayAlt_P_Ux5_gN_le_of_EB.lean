-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.gN_le_of_EB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:59:00.902914+00:00
-- url     : https://prove2.me/submissions/7258ac5d-c6e7-401d-9368-fc39346e7e28

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {k r : ℕ} (M : B.Mat k r) {c : ℝ} (h : EB M c) (hc : 0 ≤ c) :
    B.gN M ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c := by
  unfold B.gN
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (M i j) ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), c ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * c) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
end Formalism.FourierDecayAlt.P.Ux5
