-- Prove2me | solution 1 for Formalism.MainNotions.S.Gauge.mp_cF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:24.27947+00:00
-- url     : https://prove2.me/submissions/26f9f723-5e7b-4ffb-8a8e-c8051977946d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_MpUncurry
import Theorems.Thm_Formalism_MainNotions_S_Gauge_mp_uncurry

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
    MeasurePreserving (fun y : EuclideanSpace ℝ (κ × Fin 2) => fun k => (y (k, 0) : ℂ) + (y (k, 1) : ℂ) * Complex.I)
      volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (ι := κ × Fin 2)
  have h2 := MeasurePreserving.symm _ (mp_uncurry κ)
  have h3 := volume_preserving_pi (fun _ : κ => Complex.volume_preserving_equiv_pi.symm)
  exact (h3.comp h2).comp h1
end Formalism.MainNotions.S.Gauge
