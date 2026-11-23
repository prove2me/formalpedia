-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.hX2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:36.894681+00:00
-- url     : https://prove2.me/submissions/14be63b1-b2d5-4475-ba89-dac55a831b68

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution {σ : Type*} (w : σ → ℕ) (a b : σ) (n : ℕ) (h : w a + w b = n) :
    IsWeightedHomogeneous w (X a * X b : MvPolynomial σ ℚ_[p]) n := by
  rw [← h]
  first
  | exact (isWeightedHomogeneous_X ℚ_[p] w a).mul (isWeightedHomogeneous_X ℚ_[p] w b)
  | exact (isWeightedHomogeneous_X w a).mul (isWeightedHomogeneous_X w b)
  | exact (isWeightedHomogeneous_X _ w a).mul (isWeightedHomogeneous_X _ w b)
end Formalism.GM.FrozenVariableComponents
