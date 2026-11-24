-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.integrableOn_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:11.843026+00:00
-- url     : https://prove2.me/submissions/fccb56d1-4d0b-41e9-9acc-0895c15c4da7

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
theorem _root_.solution [TopologicalSpace Ω] {act : (Fin N → ℝ) → Ω → Ω} {ph : Fin N → ℝ}
    {P : Ω → ℂ} {x : Ω} {T : Set Ω} (hP : ContinuousOn P T) (hact : Continuous fun t => act t x)
    (hT : ∀ t ∈ cube N, act t x ∈ T) : IntegrableOn (integrand act ph P x) (cube N) := by
  have h1 : ContinuousOn (fun t => P (act t x)) (cube N) :=
    hP.comp hact.continuousOn (fun t ht => hT t ht)
  have h2 : Continuous (chr ph) := by
    unfold chr; fun_prop
  exact (h1.mul h2.continuousOn).integrableOn_compact isCompact_Icc
end Formalism.L2.Pj.FJ
