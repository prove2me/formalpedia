-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBF.pr_sum_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:35.114385+00:00
-- url     : https://prove2.me/submissions/669fd358-aaa4-4d95-aa3d-263e62493150

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_add_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_zero_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.PBF
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, pr_zero_fst]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_fst, ih]
end Formalism.FourierDecayAlt.P.PBF
