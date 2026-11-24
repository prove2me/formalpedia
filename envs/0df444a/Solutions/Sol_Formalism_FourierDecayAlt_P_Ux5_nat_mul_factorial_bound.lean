-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.nat_mul_factorial_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:46.868705+00:00
-- url     : https://prove2.me/submissions/f9ecf8d1-babf-4cb6-9b25-10d994ce5e0b

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
theorem _root_.solution (p : ℕ) {m x : ℝ} (_hm : 0 ≤ m) (hx : 0 < x) :
    (p : ℝ) * (m * ((p - 1).factorial * m ^ (p - 1) / x)) ≤ (p.factorial : ℝ) / x * m ^ p := by
  cases p with
  | zero => simp; positivity
  | succ q =>
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast
    apply le_of_eq
    field_simp
end Formalism.FourierDecayAlt.P.Ux5
