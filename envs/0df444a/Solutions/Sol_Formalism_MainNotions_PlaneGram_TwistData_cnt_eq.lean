-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cnt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:10.526342+00:00
-- url     : https://prove2.me/submissions/290f2348-737c-42b1-97f8-95c5c9bd7194

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fk_inj

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
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (l0 : Fin (D.nB j + D.r))
    (h : D.fk j o l0 = i) : D.cnt j o i = if l0 ∈ o then 1 else 0 := by
  unfold cnt
  rw [Finset.sum_eq_single l0]
  · rw [if_pos h]
  · intro l _ hl
    rw [if_neg]
    intro h2
    exact hl (D.fk_inj j o (h2.trans h.symm))
  · intro h2; exact absurd (Finset.mem_univ _) h2
end Formalism.MainNotions.PlaneGram.TwistData
