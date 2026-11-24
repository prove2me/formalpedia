-- Prove2me | solution 1 for Formalism.QuantumDeterminants.fdegDimV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:12:11.69167+00:00
-- url     : https://prove2.me/submissions/ea5af9bd-2023-41ae-a3f2-f77cb2bb24bd

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_HolomorphicLowKDimensionHolds
import Mathlib.LinearAlgebra.Vandermonde
import Definitions.Def_Formalism_FormalDegreeBessel_FdegFactorial
import Theorems.Thm_Formalism_QuantumDeterminants_formal_degree_dimension_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : FdegDimV := formal_degree_dimension_holds
end Formalism.QuantumDeterminants
