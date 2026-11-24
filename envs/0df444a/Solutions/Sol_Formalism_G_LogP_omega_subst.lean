-- Prove2me | solution 1 for Formalism.G.LogP.omega_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:34.898802+00:00
-- url     : https://prove2.me/submissions/14b5a5a2-830a-4408-b40a-13bff2406d7e

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_hb0
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

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
theorem _root_.solution {σ : Type*} {u : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (F : FormalGroup R) :
    (omegaF F).subst u = (MvPowerSeries.pderiv R 1 F.toPowerSeries).subst ![u, 0] := by
  have hu' : MvPowerSeries.HasSubst (fun _ : Unit => u) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)
  unfold omegaF
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hb0 hu']
  congr 1
  funext i
  fin_cases i
  · exact MvPowerSeries.subst_X hu' ()
  · exact subst_zero' hu'
end Formalism.G.LogP
