-- Prove2me | solution 1 for Formalism.FG.CongrVAux.degree_lt_of_le_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:21.848806+00:00
-- url     : https://prove2.me/submissions/db4a73f6-f109-444b-8efd-14f03062f662

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {e d : τ →₀ ℕ} (hle : e ≤ d) (hne : e ≠ d) :
    e.degree < d.degree := by
  have h2 : (d - e).degree ≠ 0 := by
    rw [Ne, Finsupp.degree_eq_zero_iff]
    intro h
    exact hne (le_antisymm hle (tsub_eq_zero_iff_le.mp h))
  have h3 : d.degree = e.degree + (d - e).degree := by
    conv_lhs => rw [← add_tsub_cancel_of_le hle]
    exact map_add _ _ _
  omega
end Formalism.FG.CongrVAux
