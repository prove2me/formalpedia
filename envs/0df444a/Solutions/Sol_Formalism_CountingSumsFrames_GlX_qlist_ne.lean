-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.qlist_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:45.484632+00:00
-- url     : https://prove2.me/submissions/c06e2de2-2cfc-408e-aec7-60f4524842ff

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
theorem _root_.solution (S : Finset (Fin r → ℤ)) (c : ℤ) : ∀ x ∈ qlist S c, x ≠ c := by
  intro x hx
  unfold qlist at hx
  rw [Finset.mem_toList] at hx
  exact Finset.ne_of_mem_erase hx
end Formalism.CountingSumsFrames.GlX
