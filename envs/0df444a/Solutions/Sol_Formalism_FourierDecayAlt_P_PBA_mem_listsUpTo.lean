-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.mem_listsUpTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:33:47.209609+00:00
-- url     : https://prove2.me/submissions/5adf59c8-fdf0-41f8-b640-34ed2d844f55

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces

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
theorem _root_.solution {T : Finset ℝ} {n : ℕ} (L : List C.Letter) (hl : L.length ≤ n)
    (hT : ∀ x ∈ L, x.2 ∈ T) : L ∈ C.listsUpTo T n := by
  unfold C.listsUpTo
  rw [Finset.mem_biUnion]
  refine ⟨L.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hl), ?_⟩
  rw [Finset.mem_image]
  refine ⟨fun i => L.get i, ?_, List.ofFn_get L⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_product]
  exact ⟨Finset.mem_univ _, hT _ (List.mem_iff_get.mpr ⟨i, rfl⟩)⟩
end Formalism.FourierDecayAlt.P.PBA
