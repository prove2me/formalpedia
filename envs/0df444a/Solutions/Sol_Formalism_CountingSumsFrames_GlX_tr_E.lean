-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.tr_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:08.335023+00:00
-- url     : https://prove2.me/submissions/fd8b3a4e-26e4-46ec-988d-236f68ebd9b6

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_E_Lv

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
theorem _root_.solution {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (a b : Fin r)
    (y : LinearMap.range (Lv G h)) (hy : G.E a b y ∈ LinearMap.range (Lv G h)) :
    tr G hk ⟨G.E a b y, hy⟩ = G.E a b (tr G hk y) := by
  obtain ⟨y, c, rfl⟩ := y
  rw [show (⟨G.E a b _, hy⟩ : LinearMap.range (Lv G h)) =
      ⟨Lv G h (Finsupp.mapDomain (List.cons (a, b)) c), LinearMap.mem_range_self _ _⟩ from
    Subtype.ext (E_Lv G h a b c), tr_apply, tr_apply, E_Lv]
end Formalism.CountingSumsFrames.GlX
