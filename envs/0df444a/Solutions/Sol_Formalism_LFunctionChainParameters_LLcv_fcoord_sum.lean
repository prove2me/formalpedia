-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.fcoord_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:01.736322+00:00
-- url     : https://prove2.me/submissions/f6666ff1-af20-4b8c-9076-c62b4ea9c00b

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_HN_HeightGram_fcoord_smul
import Theorems.Thm_Formalism_HN_PlaceDecomposition_fcoord_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
open scoped Matrix
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    {j : ℕ} (c : Fin j → K) (e : Fin j → V) :
    fcoord b X v (∑ k, c k • e k) = ∑ k, v.embedding (c k) • fcoord b X v (e k) := by
  let φ : V →+ (ι → ℂ) := AddMonoidHom.mk' (fcoord b X v) (fcoord_add b X v)
  have h : φ (∑ k, c k • e k) = ∑ k, φ (c k • e k) := map_sum φ _ _
  have h2 : ∀ x, φ x = fcoord b X v x := fun _ => rfl
  simp only [h2] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ => HeightGram.fcoord_smul b X v (c k) (e k)
end Formalism.LFunctionChainParameters.LLcv
