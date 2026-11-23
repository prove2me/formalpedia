-- Prove2me | solution 1 for Formalism.FG.InjVAux.Good.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:11.160847+00:00
-- url     : https://prove2.me/submissions/d1b34203-fa64-4f59-8794-e7c1394d00f0

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul
import Theorems.Thm_Formalism_FG_InjVAux_good_one
import Theorems.Thm_Formalism_FG_InjVAux_Good_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open Formalism.FG.InjVAux
open MvPowerSeries
variable {R : Type*} [CommRing R] {τ : Type*}
namespace Formalism.FG.InjVAux
namespace Good
theorem _root_.solution {N k : ℕ} {x x' : MvPowerSeries τ R} (hx : Good N k x x') (n : ℕ) :
    Good N (k * n) (x ^ n) (x' ^ n) := by
  induction n with
  | zero => simpa using good_one N
  | succ n ih => rw [pow_succ, pow_succ, Nat.mul_succ]; exact ih.mul hx
end Good
end Formalism.FG.InjVAux
