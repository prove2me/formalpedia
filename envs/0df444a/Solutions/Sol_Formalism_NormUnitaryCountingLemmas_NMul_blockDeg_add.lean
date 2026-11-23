-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.blockDeg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:59.138942+00:00
-- url     : https://prove2.me/submissions/b31f6133-13f6-49c1-9a67-f80ca5baccd6

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul
namespace Formalism.NormUnitaryCountingLemmas.NMul
theorem _root_.solution {N n : ℕ} (a b : Fin N × Fin n →₀ ℕ) (j : Fin N) :
    blockDeg (a + b) j = blockDeg a j + blockDeg b j := by
  simp [blockDeg, sum_add_distrib]
end Formalism.NormUnitaryCountingLemmas.NMul
