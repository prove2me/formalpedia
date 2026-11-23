-- Prove2me | solution 1 for Formalism.FG.FunctionalEquationHom.funEqV_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:46.813278+00:00
-- url     : https://prove2.me/submissions/5dad4f81-7406-4730-ab03-a2d0c0efb1bf

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Theorems.Thm_Formalism_FG_FunctionalEquationHom_integralMv_sub

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
open Formalism Formalism.FG Formalism.FG.FunctionalEquationHom
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.FunctionalEquationHom
theorem _root_.solution {ι : Type v} [Fintype ι] {τ : Type w} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) {a b : ι → MvPowerSeries τ K} (ha : IsFunEqTypeV p q hq σ M a)
    (hb : IsFunEqTypeV p q hq σ M b) : IsFunEqTypeV p q hq σ M (a - b) := by
  intro j
  convert integralMv_sub (ha j) (hb j) using 1
  simp only [Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]
  abel
end Formalism.FG.FunctionalEquationHom
