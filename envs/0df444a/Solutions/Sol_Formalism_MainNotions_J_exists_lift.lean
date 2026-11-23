-- Prove2me | solution 1 for Formalism.MainNotions.J.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:24:54.899807+00:00
-- url     : https://prove2.me/submissions/d1ce1e74-b426-4c6f-b5c0-7f17e5b4ef71

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
theorem _root_.solution (O : Subring K) (A : MvPowerSeries ι K) (h : ∀ n, coeff n A ∈ O) :
    ∃ A' : MvPowerSeries ι O, map O.subtype A' = A := by
  refine ⟨fun n => ⟨coeff n A, h n⟩, ?_⟩
  ext n
  first
  | rfl
  | (erw [MvPowerSeries.coeff_map]; rfl)
end Formalism.MainNotions.J
