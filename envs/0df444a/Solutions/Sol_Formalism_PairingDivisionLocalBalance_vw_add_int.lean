-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.vw_add_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:04.490382+00:00
-- url     : https://prove2.me/submissions/0ca8b7a7-94ad-48bf-b6ab-5bf03be716ae

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_intValuation_eq_exp
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
private theorem le_of_withZero_exp_le_exp {a b : ℤ} (h : WithZero.exp a ≤ WithZero.exp b) : a ≤ b := by
  first
  | exact WithZero.exp_le_exp.mp h
  | simpa [WithZero.exp] using h
end Val
end Formalism.PairingDivisionLocalBalance
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution (w : Pl K) (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vw w (x : K)) (vw w (y : K)) ≤ vw w ((x + y : 𝓞 K) : K) := by
  have h := w.intValuation.map_add x y
  rw [intValuation_eq_exp w x hx, intValuation_eq_exp w y hy,
    intValuation_eq_exp w (x + y) hxy] at h
  rcases le_max_iff.mp h with h1 | h1
  · have h2 := le_of_withZero_exp_le_exp h1
    exact min_le_of_left_le (by omega)
  · have h2 := le_of_withZero_exp_le_exp h1
    exact min_le_of_right_le (by omega)
end Formalism.PairingDivisionLocalBalance
