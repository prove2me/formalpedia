-- Prove2me | solution 1 for Formalism.CountingSumsFrames.glAct_wtsp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:42.173435+00:00
-- url     : https://prove2.me/submissions/dfe57939-8171-4ea4-9984-abbd07450d47

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d : Fin r) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ μ, glAct p LL j c d x ∈ WtSpC p LL j univ (shiftW μ c d) := by
  unfold WtSpC
  apply glAct_keep
  · intro i hi hvi m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    intro c' _
    unfold shiftW
    rw [(wt_shift LL j c d c' i hi m).1 hvi h1, hm c' (Finset.mem_univ c')]
  · intro i hi hvi m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    intro c' _
    unfold shiftW
    rw [(wt_shift LL j c d c' i hi m).2 hvi h1, hm c' (Finset.mem_univ c')]
end Formalism.CountingSumsFrames
