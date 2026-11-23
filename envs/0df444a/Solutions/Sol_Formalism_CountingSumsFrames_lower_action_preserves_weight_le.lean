-- Prove2me | solution 1 for Formalism.CountingSumsFrames.lower_action_preserves_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:46.989304+00:00
-- url     : https://prove2.me/submissions/6f87b494-499a-4e4a-85e1-49b2e1013335

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_keep
import Theorems.Thm_Formalism_CountingSumsFrames_wt_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (c d : Fin r) (hdc : d < c) (Mt : WithTop ℤ) :
    ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      glAct p LL j c d x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  have hc0 : ¬ c = 0 := by
    rintro rfl
    have h1 : (d : ℕ) < ((0 : Fin r) : ℕ) := hdc
    simp at h1
  apply glAct_keep
  · intro i hi hvi m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [(wt_shift LL j c d 0 i hi m).1 hvi h1, if_neg hc0]
    exact le_trans (WithTop.coe_le_coe.mpr (by split_ifs <;> omega)) hm
  · intro i hi hvi m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [(wt_shift LL j c d 0 i hi m).2 hvi h1, if_neg hc0]
    exact le_trans (WithTop.coe_le_coe.mpr (by split_ifs <;> omega)) hm
end Formalism.CountingSumsFrames
