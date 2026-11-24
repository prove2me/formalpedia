-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.lattice_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:49.971537+00:00
-- url     : https://prove2.me/submissions/2e13578c-48e5-48db-8d26-c89a72e7b5a5

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_map_baseChange_polyBC_eq_span
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_map_mem_weyl_alt
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_word_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_applyWord_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_hw_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_map_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
theorem _root_.solution : LatticeTensor := by
  intro R O _ _ _ r n hn ν
  constructor
  · rw [map_baseChange_polyBC_eq_span]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨f, hf, rfl⟩
      exact map_mem_weyl_alt R O hn ν f hf
    · apply Submodule.span_le.2
      rintro _ ⟨w, rfl⟩
      apply Submodule.subset_span
      refine ⟨applyWord R w (hw R hn ν), la_word_mem R hn ν w, ?_⟩
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
  · intro _
    rw [map_baseChange_polyBC_eq_span]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨f, hf, rfl⟩
      exact dualWeylMap R O (algebraMap R O) r n ν f hf
    · rw [standardMonomialSpanDomain O r n ν]
      apply Submodule.span_le.2
      rintro _ ⟨K, sz, hsz, I, hshape, rfl⟩
      apply Submodule.subset_span
      exact ⟨bideterminant R sz hsz I, hshape ▸ bidetMem R r n K sz hsz I, ldlat_map_bidet _ sz hsz I⟩
end Formalism.CohomologicalDescent.SL2BinomialLattices
