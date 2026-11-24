-- Prove2me | solution 1 for Formalism.GM.M.FB.hom_XX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:42.565231+00:00
-- url     : https://prove2.me/submissions/b954c6b2-1166-4775-bc10-9970776785a4

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (u v : Fin (N + 1) × Fin r) (h : wL N r u + wL N r v = 1) :
    IsWeightedHomogeneous (wL N r) (X u * X v : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 := by
  have := (MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) u).mul
    (MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) v)
  rwa [h] at this
end Formalism.GM.M.FB
