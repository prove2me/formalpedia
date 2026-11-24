-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.intValuation_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:10.571027+00:00
-- url     : https://prove2.me/submissions/04c08725-91b8-4e24-abed-cc77b1dd9017

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
theorem _root_.solution (w : Pl K) (x : 𝓞 K) (hx : x ≠ 0) :
    w.intValuation x = WithZero.exp (-(vw w (x : K))) := by
  rw [vw_ringOfIntegers_eq_count_factors_span w x hx]
  first
  | exact w.intValuation_if_neg hx
  | (rw [w.intValuation_if_neg hx])
  | (rw [IsDedekindDomain.HeightOneSpectrum.intValuation_def, if_neg hx])
end Formalism.PairingDivisionLocalBalance
