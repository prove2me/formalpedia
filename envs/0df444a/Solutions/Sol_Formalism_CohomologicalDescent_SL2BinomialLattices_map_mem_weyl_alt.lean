-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.map_mem_weyl_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:23.956481+00:00
-- url     : https://prove2.me/submissions/a41186b9-f1fa-42bc-8a39-30c5686fd75e

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_map_algebraMap_smul_alt
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_word_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_applyWord_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_hw_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
theorem _root_.solution (R O : Type) [CommRing R] [CommRing O] [Algebra R O] {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    map (algebraMap R O) f ∈ weyl O r n hn ν := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w, rfl⟩ := hg
    simp only
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
    exact la_word_mem O hn ν w
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_algebraMap_smul_alt]
    exact Submodule.smul_mem _ _ hx
end Formalism.CohomologicalDescent.SL2BinomialLattices
