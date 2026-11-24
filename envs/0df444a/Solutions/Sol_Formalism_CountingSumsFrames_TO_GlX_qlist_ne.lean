-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.qlist_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:34.249257+00:00
-- url     : https://prove2.me/submissions/5ae9c6e1-9576-46c9-99ae-4bfed7603cc7

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.TO.GlX
theorem _root_.solution (S : Finset (Fin r → ℤ)) (c : ℤ) : ∀ x ∈ qlist S c, x ≠ c := by
  intro x hx
  unfold qlist at hx
  rw [Finset.mem_toList] at hx
  exact Finset.ne_of_mem_erase hx
end Formalism.CountingSumsFrames.TO.GlX
