-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx9.psd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:40.254819+00:00
-- url     : https://prove2.me/submissions/c66a4c77-4986-4a29-8cac-ce250a8d6a32

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9
variable {α X : Type}
namespace Formalism.FourierDecayAlt.P.Jx9
theorem _root_.solution {ι : Type} {F : Finset α} (s : Finset ι) (k : ι → α → α → ℂ)
    (h : ∀ i ∈ s, A5.IsPSD F (k i)) : A5.IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i s hi ih =>
    have := psd_add (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))
    exact psd_congr this fun x _ y _ => by rw [sum_insert hi]
end Formalism.FourierDecayAlt.P.Jx9
