-- Prove2me | solution 1 for Formalism.L2.Th1.A.Wp.sig_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:27.572249+00:00
-- url     : https://prove2.me/submissions/213c9ae0-c99c-41cb-bffa-87b400ddf13a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Wp
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.Wp
theorem _root_.solution {e : K⟦X⟧} (he : HasSubst e) (r : K) : sig he (C r) = HahnSeries.C r := by
  have h : (C r : K⟦X⟧).subst e = C r := by
    rw [← PowerSeries.coe_substAlgHom he]
    exact (PowerSeries.substAlgHom he).commutes r
  rw [sig_apply, h, HahnSeries.ofPowerSeries_C]
end Formalism.L2.Th1.A.Wp
