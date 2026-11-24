-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_ddiv_sub_appL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:41:01.321029+00:00
-- url     : https://prove2.me/submissions/dcc6a5b6-e0b5-42b4-9c7f-b4131677396d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_putL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_onLetter_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_appMon_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_as_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply


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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (M : Fin r →₀ ℕ)
    (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)) (c : ℝ)
    (hder : ∀ η : Fin r →₀ ℕ, cge v c (ddiv M (monomial η (1 : K)) -
        ∑ s, if cls s = (fun a => η a % P) then
          monomial (ρ' s + P • (δ s + (divE P η - κ s))) (cf s * bin (κ s) (divE P η)) else 0))
    {a : ℝ} {G : MvPolynomial (L × Fin r) K} (hG : cge v a G) :
    cge v (a + c) (ddiv (onLetter i M) G - appL i P cls cf ρ' δ κ G) := by
  rw [ddiv_as_sum, appL, lsup_apply, ← Finset.sum_sub_distrib]
  apply cge_sum v
  intro α _
  rw [← smul_sub]
  refine cge_smul v (hG α) ?_
  rw [ddiv_onLetter_monomial, appMon_eq, ← map_sub]
  exact cge_putL v i α (hder (letE α i))
end Formalism.MainNotions.PlaneGram
