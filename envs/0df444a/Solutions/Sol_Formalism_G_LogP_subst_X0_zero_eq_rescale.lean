-- Prove2me | solution 1 for Formalism.G.LogP.subst_X0_zero_eq_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:08.378046+00:00
-- url     : https://prove2.me/submissions/96af8956-0984-402a-bf18-e5be15c2161b

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
theorem _root_.solution (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = rescale ![1, 0] Φ := by
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  fin_cases s <;> simp
end Formalism.G.LogP
