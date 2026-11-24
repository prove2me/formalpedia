-- Prove2me | solution 1 for Formalism.L2.Th1.H.slice_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:27:24.804258+00:00
-- url     : https://prove2.me/submissions/488a0c59-0b3b-43e2-b634-a257f1172419

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {n : Type*} [Fintype n]
namespace Formalism.L2.Th1.H
theorem _root_.solution (a : Fin 4) (z : Fin 4 × n → ℂ) :
    AnalyticAt ℂ (slice a : (Fin 4 × n → ℂ) → n → ℂ) z :=
  (LinearMap.toContinuousLinearMap (sliceL (n := n) a)).analyticAt z
end Formalism.L2.Th1.H
