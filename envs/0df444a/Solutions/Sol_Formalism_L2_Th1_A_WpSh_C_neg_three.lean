-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.C_neg_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:20:07.888484+00:00
-- url     : https://prove2.me/submissions/68d9e2e5-4f1d-477f-af74-126dd9c9d3e5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution : (HahnSeries.C (((-2 - 1 : ℤ)) : K) : LaurentSeries K) = -3 := by
  rw [Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_one, map_sub, map_neg, map_ofNat,
    map_one]
  norm_num
end Formalism.L2.Th1.A.WpSh
