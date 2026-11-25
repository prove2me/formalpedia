-- Prove2me | solution 1 for Formalism.MainNotions.J.exists_plift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:28.121801+00:00
-- url     : https://prove2.me/submissions/7ee0ca41-f36d-4aa3-ac26-0c866c78f33c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K : Type} [Field K]
namespace Formalism.MainNotions.J
theorem _root_.solution (O : Subring K) (a : PowerSeries K) (h : ∀ n, PowerSeries.coeff n a ∈ O) :
    ∃ a' : PowerSeries O, PowerSeries.map O.subtype a' = a := by
  refine ⟨PowerSeries.mk (fun n => ⟨PowerSeries.coeff n a, h n⟩), ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rfl
end Formalism.MainNotions.J
