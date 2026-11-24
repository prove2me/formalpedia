-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.E_Lv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:45.266242+00:00
-- url     : https://prove2.me/submissions/64f7e8fc-f62d-4505-85cd-359aefe21f55

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
theorem _root_.solution (v : V) (a b : Fin r) (c : List (Fin r × Fin r) →₀ K) :
    G.E a b (Lv G v c) = Lv G v (Finsupp.mapDomain (List.cons (a, b)) c) := by
  unfold Lv
  rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
  rfl
end Formalism.CountingSumsFrames.GlX
