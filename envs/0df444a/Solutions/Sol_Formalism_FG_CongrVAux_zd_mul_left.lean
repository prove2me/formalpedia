-- Prove2me | solution 1 for Formalism.FG.CongrVAux.zd_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:22.646956+00:00
-- url     : https://prove2.me/submissions/eb152936-ef56-4845-b70c-ffe541705e1b

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
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {d : τ →₀ ℕ} (x : MvPowerSeries τ R) {y : MvPowerSeries τ R} (hy : Zd d y) :
    Zd d (x * y) := by
  classical
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun z hz => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
  have : z.2 ≤ e := hz ▸ le_add_self
  rw [hy _ (this.trans he), mul_zero]
end Formalism.FG.CongrVAux
