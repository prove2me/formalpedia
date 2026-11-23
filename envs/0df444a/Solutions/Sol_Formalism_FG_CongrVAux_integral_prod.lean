-- Prove2me | solution 1 for Formalism.FG.CongrVAux.integral_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:21.894715+00:00
-- url     : https://prove2.me/submissions/342ecb67-f71d-403d-9483-4fab556c3b37

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one


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
theorem _root_.solution {ι : Type v} (s : Finset ι) (x : ι → MvPowerSeries τ K)
    (hx : ∀ i, IntegralMv (x i)) : IntegralMv (∏ i ∈ s, x i) :=
  Finset.prod_induction _ (fun y => IntegralMv y) (fun _ _ h₁ h₂ => IntegralSubstitution.integral_mul h₁ h₂)
    IntegralSubstitution.integral_one (fun i _ => hx i)
end Formalism.FG.CongrVAux
