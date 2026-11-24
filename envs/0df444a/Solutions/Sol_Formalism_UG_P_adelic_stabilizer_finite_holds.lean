-- Prove2me | solution 1 for Formalism.UG.P.adelic_stabilizer_finite_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:41.011252+00:00
-- url     : https://prove2.me/submissions/b3bed58d-bea1-4cd5-8db8-dd5e0f836adf

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Theorems.Thm_Formalism_UG_P_adelstab_core
import Theorems.Thm_Formalism_UG_P_adelstab_levelafC_one
import Theorems.Thm_Formalism_UG_P_adelstab_mem_stdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.AdelicStabFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef g
  refine adelstab_core σ J hτ hH hdet hdef _ (levelAf σ J) inf_le_right 1 1 one_ne_zero one_ne_zero
    ?_ ?_ g
  · intro v hv
    rw [adelstab_mem_stdLat]
    intro i
    rw [adelstab_levelafC_one, one_mul]
    exact hv i
  · intro v hv i
    rw [adelstab_levelafC_one, one_mul]
    exact (adelstab_mem_stdLat v).1 hv i
end Formalism.UG.P
