-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.W_mem_wall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:21:14.394226+00:00
-- url     : https://prove2.me/submissions/3ae03f64-0cc4-4d38-a350-9ac35c71f8e5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_len_le_cnt
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_mem_listsUpTo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (w0 : S.W) : w0.1 ∈ C.wall S.pts S.Ntop := by
  have hA : S.admitted w0.1 := And.left w0.2
  have hc : w0.1.cnt ≤ S.Ntop := And.right w0.2
  unfold C.wall
  rw [Fintype.mem_piFinset]
  intro v
  refine mem_listsUpTo (w0.1 v) ((len_le_cnt S w0.1 v).trans hc) ?_
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := (And.left hA) v j hj
  have hlen : (w0.1 v).length - j < S.Ntop + 1 := by
    have := (len_le_cnt S w0.1 v).trans hc
    omega
  have hnode : ∀ y, y ∈ S.grid v ((w0.1 v).length - j) ∪ S.grid1 v → y ∈ S.nodes v := by
    intro y hy
    unfold C.HidaSetting.nodes
    rw [Finset.mem_union] at hy ⊢
    rcases hy with hy | hy
    · left
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr hlen, hy⟩
    · right
      exact hy
  unfold C.HidaSetting.pts
  rw [Finset.mem_union]
  by_cases hb : ((w0.1 v)[j]'hj).1 = true
  · left
    rw [if_pos hb] at h1
    exact hnode _ h1
  · right
    rw [if_neg hb] at h1
    exact Finset.mem_image.mpr ⟨_, hnode _ h1, by ring⟩
end Formalism.FourierDecayAlt.P.PBA
