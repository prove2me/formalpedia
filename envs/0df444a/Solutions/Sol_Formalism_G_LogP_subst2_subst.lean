-- Prove2me | solution 1 for Formalism.G.LogP.subst2_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:06.972673+00:00
-- url     : https://prove2.me/submissions/d4d40b23-e151-4e53-b77f-560ad2bd21e7

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_hs2

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
theorem _root_.solution {σ τ : Type*} (Φ : MvPowerSeries (Fin 2) R) {u v : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) {b : σ → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    (Φ.subst ![u, v]).subst b = Φ.subst ![u.subst b, v.subst b] := by
  rw [MvPowerSeries.subst_comp_subst_apply (hs2 hu hv) hb]
  congr 1
  funext i
  fin_cases i <;> rfl
end Formalism.G.LogP
