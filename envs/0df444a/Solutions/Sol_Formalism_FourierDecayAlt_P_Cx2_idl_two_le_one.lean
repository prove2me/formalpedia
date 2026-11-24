-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.idl_two_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:13:47.525183+00:00
-- url     : https://prove2.me/submissions/cd86edb4-4e0b-4fe7-bec9-77c8a700183c

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.Cx2
theorem _root_.solution (g : ℕ) (ν : ℤ) : S6.idl E g 2 ν ≤ S6.idl E g 1 ν := by
  unfold S6.idl
  have hg1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (g : E) ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff]
    exact ⟨(g : 𝓞 E), by simp⟩
  have h2 : ((g : E) ^ (2 : ℤ)) = (g : E) * (g : E) ^ (1 : ℤ) := by
    rw [zpow_one, zpow_two]
  have key : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ (2 : ℤ)) ≤
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ (1 : ℤ)) := by
    rw [h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    calc _ ≤ 1 * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ (1 : ℤ)) := by
          first
            | exact FractionalIdeal.mul_right_mono _ hg1
            | exact FractionalIdeal.mul_le_mul_right hg1 _
            | gcongr
      _ = _ := one_mul _
  first
    | exact FractionalIdeal.mul_left_mono _ key
    | exact FractionalIdeal.mul_le_mul_left key _
    | gcongr
end Formalism.FourierDecayAlt.P.Cx2
