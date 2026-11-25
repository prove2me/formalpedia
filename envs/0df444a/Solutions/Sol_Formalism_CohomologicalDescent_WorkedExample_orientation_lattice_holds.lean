-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.orientation_lattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:57.91855+00:00
-- url     : https://prove2.me/submissions/17336da0-c7fd-4bed-b724-2f37b9f58932

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_linked_all_holds
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_reflection_carried_facts
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_exponents_from_lattice


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
theorem _root_.solution : WEOrientLattice := by
  intro ι _ σ k j t q l h _ O F L _ _ _ _ _ _ I _ W u c D cst ep J botJ kap τ ζ em jj hl hsmall hR hL
    hC hW hS
  obtain ⟨hinv, hcom, hJ, hb⟩ := reflection_carried_facts D σ h t ep J botJ hR hC
  have all := linked_all_holds ι _ D σ h t F cst hR hL
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have e1 : D.U (ep (ep τ)) = D.U τ := by rw [hinv]
  have e2 : J (ep τ) = D.U' τ := hC.2.1 τ
  have e3 : botJ (ep τ) = D.bot τ := hC.2.2 τ
  have e4 : σ (ep τ) = ep (σ τ) := hcom τ
  have e5 : botJ (ep (σ τ)) = D.bot (σ τ) := hC.2.2 _
  have e6 : D.U (ep (ep (σ τ))) = D.U (σ τ) := by rw [hinv]
  have key := FrobeniusPeriodChange.weight_exponents_from_lattice ι σ k j t q l h O F L I W u c (fun i => D.U (ep i)) J botJ
    (fun _ => 0) kap (ep τ) ζ em jj
    hl hsmall hW (fun i => (all (ep i)).1) (fun i => by rw [hJ]; exact (all (ep i)).2.1)
    (fun i s => by rw [hb]; exact (all (ep i)).2.2.1 s)
    (fun i => by rw [hJ]; exact (all (ep i)).2.2.2)
    (by intro a; show 0 ≤ D.U (ep (ep τ)) a; rw [e1]; exact hS1 a)
    (by show ∑ a, D.U (ep (ep τ)) a = _; rw [e1, e2]; exact hS2)
    (by intro a h1 h2; show D.U (ep (ep τ)) a = _; rw [e1, e3]; exact hS3 a h1 h2)
  simp only [e4, e1, e2, e3, e5, e6] at key
  exact key
end Formalism.CohomologicalDescent.WorkedExample
