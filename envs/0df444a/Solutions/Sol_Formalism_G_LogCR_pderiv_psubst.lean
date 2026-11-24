-- Prove2me | solution 1 for Formalism.G.LogCR.pderiv_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:02.437986+00:00
-- url     : https://prove2.me/submissions/a3d04f18-8038-46a1-bd87-3507ee5cded0

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogCR
variable {R : Type*} [CommRing R] {σ τ : Type*}
namespace Formalism.G.LogCR
theorem _root_.solution [Finite τ] {a : MvPowerSeries τ R} (ha : constantCoeff a = 0)
    (f : PowerSeries R) (i : τ) :
    MvPowerSeries.pderiv R i (f.subst a) =
      (PowerSeries.derivative R f).subst a * MvPowerSeries.pderiv R i a := by
  have := pderiv_subst (σ := Unit) (a := fun _ => a) (fun _ => ha) f i
  simpa [PowerSeries.subst_def, PowerSeries.derivative] using this
end Formalism.G.LogCR
