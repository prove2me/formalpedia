-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Dle_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:31.617808+00:00
-- url     : https://prove2.me/submissions/fc59db36-b54a-46ec-90dd-539637b54087

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone

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
theorem _root_.solution {μ ν κ : Fin r → ℤ} (h1 : Dle μ ν) (h2 : Dle ν κ) : Dle μ κ := ⟨fun k => (h1.1 k).trans (h2.1 k), h1.2.trans h2.2⟩
end Formalism.GM.DimensionMonotonicity
