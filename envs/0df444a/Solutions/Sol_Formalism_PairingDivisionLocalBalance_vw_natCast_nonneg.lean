-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:01.270381+00:00
-- url     : https://prove2.me/submissions/0522d249-fbb5-4f9d-8eb9-1827d6b5b169

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int_nonneg


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
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) (n : ℕ) :
    0 ≤ vw w (n : K) := by
  have := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (n : 𝓞 K)
  simpa using this
end Formalism.PairingDivisionLocalBalance
