-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Dle_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:32.740811+00:00
-- url     : https://prove2.me/submissions/d2c558eb-0d1d-48ae-989c-01a7b21d017f

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_psum_succ_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
variable {r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution {μ ν : Fin r → ℤ} (h1 : Dle μ ν) (h2 : Dle ν μ) : μ = ν := by
  funext c
  have e : ∀ k, psum μ k = psum ν k := fun k => le_antisymm (h1.1 k) (h2.1 k)
  rw [← psum_succ_sub μ c, ← psum_succ_sub ν c, e, e]
end Formalism.GM.DimensionMonotonicity
