-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.GeV.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:02.473433+00:00
-- url     : https://prove2.me/submissions/72a79b63-fde4-46bd-be54-dd55fa94a320

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
private theorem vw_mul_lemma (w : Pl K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul]
  · exact fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
  · exact fun h => hb (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
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
theorem _root_.solution {w : Pl K} {c c' : ℝ} {x y : K} (hx : GeV w c x) (hy : GeV w c' y) :
    GeV w (c + c') (x * y) := by
  unfold GeV at *
  rcases hx with hx | hx
  · left; rw [hx, zero_mul]
  rcases hy with hy | hy
  · left; rw [hy, mul_zero]
  by_cases hx0 : x = 0
  · left; rw [hx0, zero_mul]
  by_cases hy0 : y = 0
  · left; rw [hy0, mul_zero]
  right
  rw [vw_mul_lemma w x y hx0 hy0]
  push_cast
  linarith
end GeV
end Formalism.PairingDivisionLocalBalance
