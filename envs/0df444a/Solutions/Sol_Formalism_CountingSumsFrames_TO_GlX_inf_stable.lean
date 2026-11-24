-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.inf_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:08.727832+00:00
-- url     : https://prove2.me/submissions/02ca82a2-bf1f-47f1-9c4f-7e291f484986

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
theorem _root_.solution {U U' : Submodule K V} (hU : G.Stable U) (hU' : G.Stable U') : G.Stable (U ⊓ U') := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.Stable at *
  intro a b x hx
  rw [Submodule.mem_inf] at hx ⊢
  exact ⟨hU a b x hx.1, hU' a b x hx.2⟩
end Formalism.CountingSumsFrames.TO.GlX
