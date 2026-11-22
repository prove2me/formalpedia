-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:37.723624+00:00
-- url     : https://prove2.me/submissions/ffaf13e9-fc92-4302-b7d6-33591b9f03d4

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (h : F.support ⊆ s) :
    fk F G = ∑ m ∈ s, F.coeff m * G.coeff m * wf m := by
  unfold fk
  apply Finset.sum_subset h
  intro m _ hm
  rw [notMem_support_iff.mp hm]; ring
end Formalism.GM.leadingTermLemmas
