-- Prove2me | solution 1 for FreyPackage.freyCurve_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/258117e1-f9c8-5ce8-a9f1-8d98c08c3035

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_freyCurve_discriminant

open WeierstrassCurve

theorem solution (P : FreyPackage) :
    P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  have h : ((P.c : ℚ)) ^ P.p = (P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p := by
    exact_mod_cast P.hFLT.symm
  have key : ((P.a : ℚ) * P.b * P.c) ^ (2 * P.p)
      = ((P.a : ℚ) ^ P.p) ^ 2 * ((P.b : ℚ) ^ P.p) ^ 2 * ((P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p) ^ 2 := by
    rw [← h]
    ring
  rw [key]
  simp only [FreyPackage.freyCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

end S_FreyPackage_freyCurve_discriminant
end P2MW
export P2MW.S_FreyPackage_freyCurve_discriminant (solution)
