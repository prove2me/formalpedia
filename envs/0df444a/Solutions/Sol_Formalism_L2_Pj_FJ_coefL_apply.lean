-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.coefL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:15:54.238506+00:00
-- url     : https://prove2.me/submissions/d2e2d783-e125-4dd0-a72e-6f772a5da91f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Pj
open Formalism.L2.Pj.FJ
variable {Ω : Type} {N : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (act : (Fin N → ℝ) → Ω → Ω) (S : Set Ω) (ph : Fin N → ℝ) (P : OrbInt act S)
    {x : Ω} (hx : x ∈ S) : coefL act S ph P x = coefFn act ph P x := by
  simp [coefL, hx]
end Formalism.L2.Pj.FJ
