-- Prove2me | solution 1 for Formalism.G.LogP.psubst_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:54.467785+00:00
-- url     : https://prove2.me/submissions/d4690615-e94d-409e-9d4c-1ef8860372ca

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero

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
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
namespace Formalism.G.LogP
theorem _root_.solution {σ τ : Type*} (φ : PowerSeries R) {u : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (φ.subst u).subst b = φ.subst (u.subst b) := by
  have hu' : MvPowerSeries.HasSubst (fun _ : Unit => u) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hu' hb]
end Formalism.G.LogP
