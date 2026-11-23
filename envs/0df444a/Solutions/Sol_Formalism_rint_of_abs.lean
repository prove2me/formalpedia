-- Prove2me | solution 1 for Formalism.rint_of_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:12.188773+00:00
-- url     : https://prove2.me/submissions/1c037a8c-2be6-42b6-ad92-c774a47a509e

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly

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
theorem _root_.solution (f : ℝ → ℝ) (hf : Measurable f) (σ : ℝ)
    (hI : IntegrableOn (fun x : ℝ => |f x| * x ^ (-σ - 1)) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => f x * x ^ (-σ - 1)) (Ioi 1) := by
  refine Integrable.mono' hI ((hf.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
end Formalism
