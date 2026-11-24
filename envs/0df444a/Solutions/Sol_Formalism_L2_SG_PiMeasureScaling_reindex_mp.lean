-- Prove2me | solution 1 for Formalism.L2.SG.PiMeasureScaling.reindex_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:32.056807+00:00
-- url     : https://prove2.me/submissions/caba3642-5913-49c5-9f99-8e43425a9285

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_PiMeasureScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.PiMeasureScaling
namespace Formalism.L2.SG.PiMeasureScaling
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (fun (y : κ → ℂ) (i : ι) => y (e i)) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : ι => ℂ) e.symm
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) e.symm)) =
      fun (y : κ → ℂ) (i : ι) => y (e i) := by
    funext y i
    have h1 := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => ℂ) y (e i)
    simpa using h1
  rw [hf] at h
  exact h
end Formalism.L2.SG.PiMeasureScaling
