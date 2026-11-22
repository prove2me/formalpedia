-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.bin_onLetter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:14.582454+00:00
-- url     : https://prove2.me/submissions/4308ba7a-d763-499c-9ac0-7d3543376e03

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_onLetter_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    (bin (onLetter i M) α : K) = bin M (letE α i) := by
  unfold bin
  rw [Fintype.prod_prod_type, Finset.prod_eq_single i]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [onLetter_apply, if_pos rfl, letE_apply]
  · intro j _ hj
    refine Finset.prod_eq_one fun a _ => ?_
    rw [onLetter_apply, if_neg hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.MainNotions.PlaneGram
