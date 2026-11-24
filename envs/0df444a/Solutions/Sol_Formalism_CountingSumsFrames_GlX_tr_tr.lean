-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.tr_tr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:21.596807+00:00
-- url     : https://prove2.me/submissions/ac692252-3fc0-4a47-8c30-a675b23a6ec0

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
theorem _root_.solution {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h'))
    (hk' : LinearMap.ker (Lv G h') ≤ LinearMap.ker (Lv G h)) (y : LinearMap.range (Lv G h)) :
    tr G hk' ⟨tr G hk y, tr_mem G hk y⟩ = y := by
  obtain ⟨y, c, rfl⟩ := y
  have e : (⟨tr G hk ⟨Lv G h c, LinearMap.mem_range_self _ c⟩, tr_mem G hk _⟩ : LinearMap.range (Lv G h')) =
      ⟨Lv G h' c, LinearMap.mem_range_self _ c⟩ := Subtype.ext (tr_apply G hk c)
  rw [e, tr_apply]
end Formalism.CountingSumsFrames.GlX
