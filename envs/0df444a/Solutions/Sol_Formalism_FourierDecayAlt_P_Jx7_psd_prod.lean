-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.psd_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:00.761342+00:00
-- url     : https://prove2.me/submissions/f90535b6-1905-4570-82ee-da8f485c021e

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_one

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
theorem _root_.solution {P : Type} (s : Finset P) (k : P → α → α → ℂ) (hk : ∀ p ∈ s, TB.PSDOn F (k p)) :
    TB.PSDOn F (fun x y => ∏ p ∈ s, k p x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_one
  | insert a s ha ih =>
    have h1 := psd_mul (hk a (Finset.mem_insert_self a s))
      (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ h1
    intro x _ y _
    rw [Finset.prod_insert ha]
end Formalism.FourierDecayAlt.P.Jx7
