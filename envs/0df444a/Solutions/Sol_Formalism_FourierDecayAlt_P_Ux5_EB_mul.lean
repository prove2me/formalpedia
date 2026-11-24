-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.EB_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:21:25.596947+00:00
-- url     : https://prove2.me/submissions/a7615fed-cd8f-4e83-b542-57aa01809d34

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
theorem _root_.solution {l m n : Type*} [Fintype m] {A : Matrix l m ℂ} {B : Matrix m n ℂ} {a b : ℝ}
    (hA : EB A a) (hB : EB B b) : EB (A * B) (Fintype.card m * (a * b)) := by
  intro i k
  rw [mul_apply]
  calc ‖∑ j, A i j * B j k‖ ≤ ∑ j, ‖A i j * B j k‖ := norm_sum_le _ _
    _ ≤ ∑ _j : m, a * b := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hA i j) (hB j k) (norm_nonneg _) ((norm_nonneg _).trans (hA i j))
    _ = Fintype.card m * (a * b) := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end Formalism.FourierDecayAlt.P.Ux5
