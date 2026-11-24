-- Prove2me | solution 1 for Formalism.L2.Th1.A.flowZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:49:05.850141+00:00
-- url     : https://prove2.me/submissions/b9d095b7-f1c9-4535-8d96-0da70c050638

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
import Theorems.Thm_Formalism_L2_Th1_A_Wp_isFlow_sig
import Theorems.Thm_Formalism_L2_Th1_A_Wp_mul_yZ_sig

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
open Wp
namespace Formalism.L2.Th1.A
theorem _root_.solution (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : FlowZ.{u} := by
  intro K _ _ W
  obtain ⟨h0, h1, -, -, -⟩ := hE K W
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' h0
  have inj : Function.Injective (toL : K⟦X⟧ →+* LaurentSeries K) := HahnSeries.ofPowerSeries_injective
  have hne : toL (expSer W) ≠ 0 := by
    intro h
    have h' : expSer W = 0 := inj (by rw [h, map_zero])
    rw [h', map_zero] at h1
    exact zero_ne_one h1
  exact ⟨Wp.isFlow_sig W he (hC K W) hne, Wp.mul_yZ_sig W he hne⟩
end Formalism.L2.Th1.A
