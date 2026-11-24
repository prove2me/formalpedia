-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.card_unmarked
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:17.346798+00:00
-- url     : https://prove2.me/submissions/50a94a68-4152-4e65-bf5b-34fa0f47d69e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding

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
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (hM : ¬ D.Marked j o) (m : Fin D.r) :
    (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card < D.r := by
  have h1 : (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card ≤
      (Finset.Ico (D.nB j) (D.stg j m)).card := by
    refine Finset.card_le_card_of_injOn (fun l => l.val) ?_ ?_
    · intro l hl
      have hl' := Finset.mem_filter.mp (Finset.mem_coe.mp hl)
      simp only [Finset.coe_Ico, Set.mem_Ico]
      refine ⟨?_, hl'.2.1⟩
      by_contra hlt
      exact hM ⟨l, hl'.1, not_le.mp hlt⟩
    · intro x _ y _ h
      exact Fin.ext h
  rw [Nat.card_Ico] at h1
  have := m.2
  have h2 : D.stg j m - D.nB j < D.r := by unfold stg; omega
  omega
end Formalism.MainNotions.PlaneGram.TwistData
