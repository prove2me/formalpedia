-- Prove2me | solution 1 for Formalism.UG.P.hermitian_form_symmetry_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:54.767379+00:00
-- url     : https://prove2.me/submissions/6bf9b70b-23f2-4894-847e-9eda282eed37

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Theorems.Thm_Formalism_UG_P_csEasy_formJ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.FormSymm := by
  intro E _ σ hσ n _ _ J c hc hJ
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using this
  refine ⟨?_, fun x y => csEasy_formJ_apply σ hσ J c x y⟩
  constructor
  intro x y
  rw [csEasy_formJ_apply, csEasy_formJ_apply]
  show σ (c * Formalism.UG.hform σ J x y) = c * Formalism.UG.hform σ J y x
  rw [map_mul, hc]
  congr 1
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Formalism.UG.P
