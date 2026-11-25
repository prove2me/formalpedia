-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.orientation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:11.751384+00:00
-- url     : https://prove2.me/submissions/83af37d3-cbe9-4772-955f-ccf37b1eab4d

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_linked_all_holds
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_reflection_carried_facts
import Theorems.Thm_Formalism_CohomologicalDescent_weightExchangeFull_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : WEOrient := by
  intro ι _ σ k j t q l h F _ _ W D cst ep J botJ kap c τ hl hsmall hR hL hC hW hs hk hS hU'h hc
  obtain ⟨hinv, hcom, hJ, hb⟩ := reflection_carried_facts D σ h t ep J botJ hR hC
  have all := linked_all_holds ι _ D σ h t F cst hR hL
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have e1 : D.U (ep (ep τ)) = D.U τ := by rw [hinv]
  have e2 : J (ep τ) = D.U' τ := hC.2.1 τ
  have e3 : botJ (ep τ) = D.bot τ := hC.2.2 τ
  have e4 : σ (ep τ) = ep (σ τ) := hcom τ
  have e5 : botJ (ep (σ τ)) = D.bot (σ τ) := hC.2.2 _
  have e6 : D.U (ep (ep (σ τ))) = D.U (σ τ) := by rw [hinv]
  have key := weightExchangeFull_holds ι σ k j t q l h F W (fun i => D.U (ep i)) J botJ (fun _ => 0) kap c (ep τ)
    hl hsmall hW hs hk (fun i => (all (ep i)).1) (fun i => by rw [hJ]; exact (all (ep i)).2.1)
    (fun i s => by rw [hb]; exact (all (ep i)).2.2.1 s)
    (fun i => by rw [hJ]; exact (all (ep i)).2.2.2)
    (by intro a; show 0 ≤ D.U (ep (ep τ)) a; rw [e1]; exact hS1 a)
    (by intro a; rw [e2]; exact hU'h a)
    (by show ∑ a, D.U (ep (ep τ)) a = _; rw [e1, e2]; exact hS2)
    (by intro a h1 h2; show D.U (ep (ep τ)) a = _; rw [e1, e3]; exact hS3 a h1 h2)
    (by rw [e2]; exact hc)
  simp only [e4, e1, e2, e3, e5, e6] at key
  exact key
end Formalism.CohomologicalDescent.WorkedExample
