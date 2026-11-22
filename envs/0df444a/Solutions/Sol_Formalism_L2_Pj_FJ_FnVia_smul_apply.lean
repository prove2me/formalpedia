-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.FnVia.smul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:02.55956+00:00
-- url     : https://prove2.me/submissions/ffab28c9-af87-47a0-8960-c8eb15bcd570

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
variable {K : Type} [Field K]
variable (σ : K →+* ℂ) (Ω : Type)
variable {σ Ω}
namespace Formalism.L2.Pj.FJ
namespace FnVia
theorem _root_.solution (a : K) (f : FnVia σ Ω) (x : Ω) :
    (show Ω → ℂ from a • f) x = σ a * (show Ω → ℂ from f) x := rfl
end FnVia
end Formalism.L2.Pj.FJ
