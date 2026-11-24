-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x3_tel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:23.987896+00:00
-- url     : https://prove2.me/submissions/1557ec22-49fa-4ff3-b7a3-888c2a3caba2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (y : ℕ → ℝ) (hy : ∀ i, y i ≠ 0) :
    ∀ n, ∏ l ∈ Finset.range n, y (l + 1) / y l = y n / y 0 := by
  intro n
  induction n with
  | zero => simp [div_self (hy 0)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, div_mul_div_comm, mul_comm (y n) (y (n + 1)),
      mul_div_mul_right _ _ (hy n)]
end Formalism.FourierDecayAlt.P
