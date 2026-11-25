-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.costA_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:19.81624+00:00
-- url     : https://prove2.me/submissions/813286fd-b0a6-4216-b3f0-31e28da21e51

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ChOK_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_costM_ok
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution : CostOK (D.CostA p) where
  one := fun _ => D.costM_ok.one
  mul := fun m n _ _ hf hg ρ => D.costM_ok.mul m n _ _ (hf ρ) (hg ρ)
  add := fun n _ _ hf hg ρ => D.costM_ok.add n _ _ (hf ρ) (hg ρ)
  smul := fun n a _ hf ρ => D.costM_ok.smul n a _ (hf ρ)
  mono := fun m n _ hmn hf ρ => D.costM_ok.mono m n _ hmn (hf ρ)
end Formalism.MainNotions.PlaneGram.TwistData
