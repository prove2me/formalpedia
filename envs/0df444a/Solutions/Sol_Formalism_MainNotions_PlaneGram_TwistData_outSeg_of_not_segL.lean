-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.outSeg_of_not_segL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:15.291367+00:00
-- url     : https://prove2.me/submissions/daebe6da-a52c-48f1-ac1a-92fc9d48d995

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg

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
theorem _root_.solution (i : D.ML) (hi : ¬ D.SegL j i) : D.outSeg j i := by
  rintro ⟨k, rfl⟩
  apply hi
  unfold SegL
  cases k using Fin.addCases with
  | left a =>
    rw [first_embedding_castAdd]
    exact Or.inl ⟨D.eB j a, (Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2, rfl⟩
  | right m =>
    rw [first_embedding_natAdd]
    exact Or.inr (Or.inl ⟨Fin.rev m, rfl⟩)
end Formalism.MainNotions.PlaneGram.TwistData
