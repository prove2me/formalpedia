-- Prove2me | solution 1 for Formalism.G0.ManyOrbitsP.add_pow_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:56.521814+00:00
-- url     : https://prove2.me/submissions/8f18e1fc-a366-4157-9c60-95d52198203e

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP
namespace Formalism.G0.ManyOrbitsP
theorem _root_.solution (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) :
    p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k ≤ (p + q) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpq : 0 ≤ p + q := add_nonneg hp hq
    have h1 := mul_le_mul_of_nonneg_left ih hpq
    have h2 : 0 ≤ ((k : ℝ) + 1) * q ^ 2 * p ^ k := by positivity
    have e : (p + q) * (p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k) -
        (p ^ (k + 1 + 1) + (((k : ℝ) + 1) + 1) * q * p ^ (k + 1)) = ((k : ℝ) + 1) * q ^ 2 * p ^ k := by
      ring
    have e2 : (p + q) * (p + q) ^ (k + 1) = (p + q) ^ (k + 1 + 1) := by ring
    push_cast
    linarith
end Formalism.G0.ManyOrbitsP
