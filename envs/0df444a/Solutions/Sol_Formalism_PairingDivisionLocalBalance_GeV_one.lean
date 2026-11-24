-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.GeV.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:56:58.89708+00:00
-- url     : https://prove2.me/submissions/f7544dea-66cb-4003-ae34-0c5d6ae6ff74

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_of_eq_zero
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.PairingDivisionLocalBalance
namespace GeV
theorem _root_.solution (w : Pl K) : GeV w 0 (1 : K) := by
  apply GeV.of_eq_zero
  have h0 := vw_pow w (1 : K) one_ne_zero 0
  simpa using h0
end GeV
end Formalism.PairingDivisionLocalBalance
