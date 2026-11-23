-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.psd_prod_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:41.649239+00:00
-- url     : https://prove2.me/submissions/1f4c26fb-1f82-4627-97e0-3fb502e1d070

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_prod

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
theorem _root_.solution {P : Type} (s : Finset P) (k K : P → α → α → ℂ) (hk : ∀ p ∈ s, TB.PSDOn F (k p))
    (hd : ∀ p ∈ s, TB.PSDOn F (fun x y => K p x y - k p x y)) :
    TB.PSDOn F (fun x y => ∏ p ∈ s, K p x y - ∏ p ∈ s, k p x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero
  | insert a s ha ih =>
    have hka := hk a (Finset.mem_insert_self a s)
    have hda := hd a (Finset.mem_insert_self a s)
    have hKa : TB.PSDOn F (K a) := psd_congr (fun x _ y _ => by ring) (psd_add hda hka)
    have h1 := psd_mul hKa (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi)))
    have h2 := psd_mul hda (psd_prod s k (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ (psd_add h1 h2)
    intro x _ y _
    rw [Finset.prod_insert ha, Finset.prod_insert ha]; ring
end Formalism.FourierDecayAlt.P.Jx7
