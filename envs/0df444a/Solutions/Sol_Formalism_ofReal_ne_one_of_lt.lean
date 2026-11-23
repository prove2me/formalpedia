-- Prove2me | solution 1 for Formalism.ofReal_ne_one_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:12.222673+00:00
-- url     : https://prove2.me/submissions/6d182e1d-1d5e-4b1d-b677-cec7a8fd99ef

import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution {σ : ℝ} (h : σ < 1) : (σ : ℂ) ≠ 1 := by
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith
end Formalism
