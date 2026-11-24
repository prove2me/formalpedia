-- Prove2me | solution 1 for Formalism.MainNotions.S.Gauge.mp_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:41.259253+00:00
-- url     : https://prove2.me/submissions/c3d500a8-3bc2-4b06-ac13-022bb8a454a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_MpUncurry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
namespace Formalism.MainNotions.S.Gauge
theorem _root_.solution (κ : Type*) [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry κ (Fin 2) ℝ).symm volume volume := by
  refine ⟨(MeasurableEquiv.curry κ (Fin 2) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq (fun s _ => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : ((MeasurableEquiv.curry κ (Fin 2) ℝ).symm) ⁻¹' (univ.pi s) =
      univ.pi (fun k => univ.pi (fun i => s (k, i))) := by
    ext x; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
  rw [hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [Fintype.prod_prod_type]
end Formalism.MainNotions.S.Gauge
