-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.GeV.int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:40.043976+00:00
-- url     : https://prove2.me/submissions/7862bf98-a388-4807-8fa2-69b7822923d7

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
namespace Formalism.PairingDivisionLocalBalance
section Val
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem vw_ringOfIntegers_eq_count_factors_span (w : Pl K) (x : 𝓞 K) (hx : x ≠ 0) :
    vw w (x : K) = ((Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {x})).factors : ℤ) := by
  unfold Formalism.DivisionValues.vw
  rw [show (x : K) = algebraMap (𝓞 K) K x from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe]
  simpa using hx
end Val
end Formalism.PairingDivisionLocalBalance
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.PairingDivisionLocalBalance
namespace GeV
theorem _root_.solution (w : Pl K) (x : 𝓞 K) : GeV w 0 (x : K) := by
  unfold GeV
  by_cases hx : x = 0
  · left
    rw [hx]
    first
    | rfl
    | simp
    | exact map_zero (algebraMap (𝓞 K) K)
  right
  rw [vw_ringOfIntegers_eq_count_factors_span w x hx]
  positivity
end GeV
end Formalism.PairingDivisionLocalBalance
