-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ddiv_onLetter_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:11.212783+00:00
-- url     : https://prove2.me/submissions/0ff34661-49b4-4fd8-ae4e-70f93115cd94

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bin_onLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_sub_onLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_putL_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    ddiv (onLetter i M) (monomial α (1 : K)) = putL i α (ddiv M (monomial (letE α i) 1)) := by
  rw [ddiv_monomial', ddiv_monomial', putL_monomial, sub_onLetter, bin_onLetter]
end Formalism.MainNotions.PlaneGram
