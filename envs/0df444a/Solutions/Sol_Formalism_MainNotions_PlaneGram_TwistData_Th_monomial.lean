-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Th_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:47.899292+00:00
-- url     : https://prove2.me/submissions/26b7db92-14ba-4094-bded-a2777741ff64

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_TT_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_monomial


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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ζ : D.EM) :
    D.Th j cc PP (monomial ζ 1) =
      monomial (eOut (D.outSeg j) ζ) 1 * ∑ b, cc (D.pullE j ζ) b • PP b := by
  simp only [Th, lsup_monomial, one_smul, TT_monomial]
end Formalism.MainNotions.PlaneGram.TwistData
