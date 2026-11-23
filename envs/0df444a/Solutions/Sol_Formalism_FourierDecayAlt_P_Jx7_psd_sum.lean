-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.psd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:45.2097+00:00
-- url     : https://prove2.me/submissions/d0f3f2ef-fe74-4807-8718-2eb137ab2d1a

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix
variable {α : Type} {F : Finset α}
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution {ι : Type} (s : Finset ι) (k : ι → α → α → ℂ) (hk : ∀ i ∈ s, TB.PSDOn F (k i)) :
    TB.PSDOn F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero
  | insert a s ha ih =>
    have h1 := psd_add (hk a (Finset.mem_insert_self a s))
      (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ h1
    intro x _ y _
    rw [Finset.sum_insert ha]
end Formalism.FourierDecayAlt.P.Jx7
