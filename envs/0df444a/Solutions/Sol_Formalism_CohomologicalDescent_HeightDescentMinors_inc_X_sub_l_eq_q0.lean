-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.inc_X_sub_l_eq_q0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:33.4641+00:00
-- url     : https://prove2.me/submissions/a4befbeb-35d8-49d9-b895-f8ae1c482e5e

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_pi0_alt

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
theorem _root_.solution : inc l O (X - C (l : O)) = q0 l O := by
  have hs := hasSubst_pi0_alt l O
  rw [inc, ← PowerSeries.coe_substAlgHom hs, map_sub, q0]
  congr 1
  · rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
  calc PowerSeries.substAlgHom hs (C (l : O)) = PowerSeries.substAlgHom hs ((l : O) • 1) := by
        rw [PowerSeries.smul_eq_C_mul, mul_one]
    _ = (l : O) • PowerSeries.substAlgHom hs 1 := map_smul _ _ _
    _ = C (l : O) := by rw [map_one, PowerSeries.smul_eq_C_mul, mul_one]
end Formalism.CohomologicalDescent.HeightDescentMinors
