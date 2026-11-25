-- Prove2me | solution 1 for Formalism.L2.Th1.A.More.map_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:38.700514+00:00
-- url     : https://prove2.me/submissions/ebaa5113-f423-4431-8278-c66b9d5d93f7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.More
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
namespace Formalism.L2.Th1.A.More
theorem _root_.solution (φ : R →+* S) (f : R⟦X⟧) :
    PowerSeries.map φ (derivative R f) = derivative S (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]
end Formalism.L2.Th1.A.More
