-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.act_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:21.621138+00:00
-- url     : https://prove2.me/submissions/5edc8af2-4650-4032-8cb8-0d6e62c9e45d

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.GlX
theorem _root_.solution {U : Submodule K V} (hU : G.Stable U) (w : List (Fin r × Fin r)) {x : V} (hx : x ∈ U) :
    act G w x ∈ U := by
  induction w with
  | nil => exact hx
  | cons ab w ih => exact hU ab.1 ab.2 _ ih
end Formalism.CountingSumsFrames.GlX
