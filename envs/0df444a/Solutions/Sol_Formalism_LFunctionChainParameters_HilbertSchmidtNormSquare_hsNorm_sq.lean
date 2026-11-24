-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsNorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:33.950851+00:00
-- url     : https://prove2.me/submissions/9ac2ed8e-bb5a-4625-bd7f-f95f83eea1fe

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {m n : Type} [Fintype m] [Fintype n]
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (M : Matrix m n ℂ) : hsNorm M ^ 2 = hsSq M :=
  Real.sq_sqrt (hsSq_nonneg M)
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
