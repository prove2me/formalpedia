-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.gram_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:34.513064+00:00
-- url     : https://prove2.me/submissions/50828d6f-666a-4d22-94ba-4d0ab9ccf1e6

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_HN_HeightGram_norm_det_gramPl
import Theorems.Thm_Formalism_HN_height_gram_determinant
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_pos


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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {j : ℕ} (e : Fin j → V) (he : LinearIndependent K e)
    (v : InfinitePlace K) : 0 < (gramPl b X v e).det.re ∧ (gramPl b X v e).det.im = 0 := by
  have hn := fun w => HeightGram.norm_det_gramPl b X w e
  have hprod := (height_gram_determinant K V ι b X hX j e he).1
  have hpos : 0 < ∏ w, (gramPl b X w e).det.re := by
    rw [← hprod]; exact ht_pos b X hX (Submodule.fg_span (Set.finite_range e))
  have h0 : (gramPl b X v e).det.re ≠ 0 := by
    intro h0
    rw [Finset.prod_eq_zero (Finset.mem_univ v) h0] at hpos
    exact lt_irrefl _ hpos
  have hge : 0 ≤ (gramPl b X v e).det.re := by rw [← hn v]; exact norm_nonneg _
  refine ⟨lt_of_le_of_ne hge h0.symm, ?_⟩
  apply (Complex.abs_re_eq_norm).1
  rw [hn v, abs_of_nonneg hge]
end Formalism.LFunctionChainParameters.LLcv
