-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.bweight_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:59.147079+00:00
-- url     : https://prove2.me/submissions/318d70ed-a015-4f97-8272-d0de9ec11f9a

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
theorem _root_.solution {N n : ℕ} (e : Fin N × Fin n →₀ ℕ) : 0 < bweight e := by
  unfold bweight
  positivity
end Formalism.NormUnitaryCountingLemmas.NMul
