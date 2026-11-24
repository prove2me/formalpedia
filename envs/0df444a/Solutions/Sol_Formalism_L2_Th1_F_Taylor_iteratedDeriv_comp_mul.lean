-- Prove2me | solution 1 for Formalism.L2.Th1.F.Taylor.iteratedDeriv_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:24:53.06788+00:00
-- url     : https://prove2.me/submissions/b53b14d5-a826-4503-8767-3e172384c4a5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Taylor
open PowerSeries
namespace Formalism.L2.Th1.F.Taylor
theorem _root_.solution (a : ℂ) (n : ℕ) : ∀ f : ℂ → ℂ, AnalyticAt ℂ f 0 →
    iteratedDeriv n (fun z => f (a * z)) 0 = a ^ n * iteratedDeriv n f 0 := by
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have hc : Filter.Tendsto (fun z : ℂ => a * z) (nhds 0) (nhds 0) := by
      have : Continuous fun z : ℂ => a * z := by fun_prop
      simpa using this.tendsto 0
    have he : deriv (fun z => f (a * z)) =ᶠ[nhds 0] fun z => a * deriv f (a * z) := by
      filter_upwards [hc.eventually hf.eventually_analyticAt] with z hz
      have h1 : HasDerivAt f (deriv f (a * z)) (a * z) := hz.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun z : ℂ => a * z) a z := by
        simpa using (hasDerivAt_id z).const_mul a
      have := (h1.comp z h2).deriv
      rw [mul_comm] at this
      exact this
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq, iteratedDeriv_const_mul_field, ih _ hf.deriv,
      iteratedDeriv_succ', pow_succ]
    ring
end Formalism.L2.Th1.F.Taylor
