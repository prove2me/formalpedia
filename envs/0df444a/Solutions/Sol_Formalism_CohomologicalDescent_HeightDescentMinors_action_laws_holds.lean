-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.action_laws_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:07.223817+00:00
-- url     : https://prove2.me/submissions/5eb9b6a1-e74b-44b7-ba3b-f9d0e854a8da

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_subst_X_eq_self
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_br_padic
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialSeriesSubOne_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialAction_binomialSeriesSubOne
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialAction_comp_eq_mul
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_phi_eq_act_l

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : ActLaws := by
  intro l _ O _ _
  refine ⟨binomialAction_binomialSeriesSubOne l O, binomialAction_comp_eq_mul l O, ?_, phi_eq_act_l l O, ?_, ?_, ?_⟩
  · intro f
    rw [act, binomialSeriesSubOne_one, subst_X_eq_self]
  · intro c f
    rw [phi_eq_act_l, phi_eq_act_l, binomialAction_comp_eq_mul, binomialAction_comp_eq_mul, mul_comm]
  · intro c f g
    have hs := hasSubst_br_padic l O c
    refine ⟨?_, ?_⟩
    · rw [act, act, act, ← PowerSeries.coe_substAlgHom hs, map_mul]
    · rw [act, act, act, ← PowerSeries.coe_substAlgHom hs, map_add]
  · intro c a
    have hs := hasSubst_br_padic l O c
    rw [act, ← PowerSeries.coe_substAlgHom hs]
    calc PowerSeries.substAlgHom hs (C a) = PowerSeries.substAlgHom hs (a • 1) := by
          rw [PowerSeries.smul_eq_C_mul, mul_one]
      _ = a • PowerSeries.substAlgHom hs 1 := map_smul _ _ _
      _ = C a := by rw [map_one, PowerSeries.smul_eq_C_mul, mul_one]
end Formalism.CohomologicalDescent.HeightDescentMinors
