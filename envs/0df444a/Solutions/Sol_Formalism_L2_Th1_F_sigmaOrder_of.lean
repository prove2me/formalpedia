-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaOrder_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:13.438806+00:00
-- url     : https://prove2.me/submissions/a8998345-1f97-4075-b4f6-389cae4f95b8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution (he : SigmaEntire) (hz : SigmaZero) (hs : SigmaSimple) : SigmaOrder := by
  intro L a b z ha
  classical
  set f : ℂ → ℂ := fun w => wSigma L (a * w + b) with hfdef
  have hlin : Differentiable ℂ (fun w : ℂ => a * w + b) :=
    (differentiable_id.const_mul a).add_const b
  have hfd : Differentiable ℂ f := (he L).comp hlin
  have hfa : AnalyticAt ℂ f z := hfd.analyticAt z
  have hder : HasDerivAt f (deriv (wSigma L) (a * z + b) * (a * 1)) z := by
    have h1 : HasDerivAt (fun w : ℂ => a * w + b) (a * 1) z :=
      ((hasDerivAt_id z).const_mul a).add_const b
    exact ((he L) (a * z + b)).hasDerivAt.comp z h1
  rw [hfa.meromorphicOrderAt_eq]
  split_ifs with hmem
  · have h0 : f z = 0 := (hz L (a * z + b)).2 hmem
    have hord : analyticOrderAt f z = ((1 : ℕ) : ℕ∞) := by
      rw [hfa.analyticOrderAt_eq_natCast]
      refine ⟨dslope f z, ?_, ?_, ?_⟩
      · have hon : DifferentiableOn ℂ (dslope f z) Set.univ :=
          (Complex.differentiableOn_dslope Filter.univ_mem).2 hfd.differentiableOn
        exact (differentiableOn_univ.1 hon).analyticAt z
      · rw [dslope_same, hder.deriv]
        exact mul_ne_zero ((hs L).2 _ hmem) (by simpa using ha)
      · filter_upwards with w
        rw [pow_one, sub_smul_dslope, h0, sub_zero]
    rw [hord]
    rfl
  · have hne : f z ≠ 0 := fun h => hmem ((hz L (a * z + b)).1 h)
    have hord : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [hord]
    rfl
end Formalism.L2.Th1.F
