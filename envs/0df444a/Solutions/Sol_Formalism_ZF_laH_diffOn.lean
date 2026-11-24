-- Prove2me | solution 1 for Formalism.ZF.laH_diffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:18.01922+00:00
-- url     : https://prove2.me/submissions/31571e16-591b-472e-918b-7785da35d191

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (y : ℝ) (hy : 0 < y) : DifferentiableOn ℂ (laHfun y) laU := by
  intro s hs
  have hZ : riemannZeta₁ s ≠ 0 := hs.1
  have h0 : s ≠ 0 := hs.2
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  apply DifferentiableAt.differentiableWithinAt
  have hd : DifferentiableAt ℂ (deriv riemannZeta₁) s := differentiable_riemannZeta₁.deriv s
  have hz : DifferentiableAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁ s
  have hc : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hy0)
  exact ((differentiableAt_const _).sub ((differentiableAt_id.sub_const 1).mul
    (hd.div hz hZ))).mul (hc.div differentiableAt_id h0)
end Formalism.ZF
