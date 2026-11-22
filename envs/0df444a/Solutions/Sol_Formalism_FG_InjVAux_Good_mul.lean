-- Prove2me | solution 1 for Formalism.FG.InjVAux.Good.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:44.63139+00:00
-- url     : https://prove2.me/submissions/3cdf2c96-404c-4bd5-937a-7fe64da4b27a

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mono
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul

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
theorem _root_.solution {N k l : ℕ} {x x' y y' : MvPowerSeries τ R} (hx : Good N k x x')
    (hy : Good N l y y') : Good N (k + l) (x * y) (x' * y') := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨hx1.mul hy1, hx2.mul hy2, ?_⟩
  have e : x * y - x' * y' = x * (y - y') + (x - x') * y' := by ring
  rw [e]
  exact ((hx1.mul hy3).mono (by omega)).add ((hx3.mul hy2).mono (by omega))
end Good
end Formalism.FG.InjVAux
