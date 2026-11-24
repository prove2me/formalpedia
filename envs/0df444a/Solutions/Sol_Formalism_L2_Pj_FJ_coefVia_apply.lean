-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.coefVia_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:22:02.847889+00:00
-- url     : https://prove2.me/submissions/438ceb36-bd77-4a9e-a18b-bd59d8c0297c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Theorems.Thm_Formalism_L2_Pj_FJ_coefL_apply

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
theorem _root_.solution {N : ℕ} {C : Type} [AddCommGroup C] [Module K C]
    (act : (Fin N → ℝ) → Ω → Ω) (S : Set Ω) (ph : Fin N → ℝ) (rd : C →ₛₗ[σ] (Ω → ℂ))
    (hrd : ∀ F, rd F ∈ OrbInt act S) (F : C) {x : Ω} (hx : x ∈ S) :
    (coefVia act S ph rd hrd F : Ω → ℂ) x = coefFn act ph (rd F) x :=
  coefL_apply act S ph _ hx
end Formalism.L2.Pj.FJ
