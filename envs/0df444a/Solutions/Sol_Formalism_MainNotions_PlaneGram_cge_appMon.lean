-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_appMon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:23.673928+00:00
-- url     : https://prove2.me/submissions/6b511488-a620-4b43-9526-35e0775fc093

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_bin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero_iff


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
variable {I : Type} [Fintype I]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K)
    (ρ' δ κ : I → (Fin r →₀ ℕ)) (hcf : ∀ s, 0 ≤ v (cf s)) (α : L × Fin r →₀ ℕ) :
    cge v 0 (appMon i P cls cf ρ' δ κ α) := by
  unfold appMon
  apply cge_sum v
  intro s _
  by_cases h : cls s = (fun a => α (i, a) % P)
  · rw [if_pos h]
    refine cge_monomial v _ ?_
    have h2 := vge_mul v ((vge_zero_iff v (cf s)).2 (hcf s))
      (vge_bin v (κ s) (divE P (letE α i)))
    rwa [add_zero] at h2
  · rw [if_neg h]
    exact cge_zero v 0
end Formalism.MainNotions.PlaneGram
