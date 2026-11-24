-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.TT_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:15.310237+00:00
-- url     : https://prove2.me/submissions/916aaae8-9448-412f-be50-b4ee18409d2e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
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
theorem _root_.solution (lam : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) :
    D.TT j cc PP (monomial lam 1) = ∑ b, cc lam b • PP b := by
  simp only [TT, lsup_monomial, one_smul]
end Formalism.MainNotions.PlaneGram.TwistData
