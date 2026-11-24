-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.iSup_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:12.171068+00:00
-- url     : https://prove2.me/submissions/df03a827-a8cb-447b-ba44-23b9f50ce87c

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
theorem _root_.solution {ι : Sort*} {U : ι → Submodule K V} (hU : ∀ i, G.Stable (U i)) : G.Stable (⨆ i, U i) := by
  intro a b x hx
  have hle : (⨆ i, U i) ≤ (⨆ i, U i).comap (G.E a b) :=
    iSup_le fun i y hy => Submodule.mem_iSup_of_mem i (hU i a b y hy)
  exact hle hx
end Formalism.CountingSumsFrames.GlX
