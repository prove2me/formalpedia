-- Prove2me | solution 1 for Formalism.ZF.zfo_zero_re_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:05.268797+00:00
-- url     : https://prove2.me/submissions/3f023b5e-1646-4982-afdd-b2ddb5d5b49b

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoTermReNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {ρ : ℂ} {σ : ℝ} (hσ : 1 < σ) (h : riemannZeta ρ = 0) : ρ.re < σ := by
  by_contra hc
  push_neg at hc
  exact riemannZeta_ne_zero_of_one_lt_re (lt_of_lt_of_le hσ hc) h
end Formalism.ZF
