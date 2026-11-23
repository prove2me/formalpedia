-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:38.534808+00:00
-- url     : https://prove2.me/submissions/9b3e34b4-4b3f-4a6c-85fa-43eab670cb86

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CubeR
open Univ CurveSer
local notation "cc" => MvPowerSeries.constantCoeff
variable {σ : Type*} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
namespace Formalism.L2.Th1.A.CubeR
theorem _root_.solution (c : MvPowerSeries σ K₀) (h : ∀ d, MvPowerSeries.coeff d c ∈ Formalism.ELL.coeffRing WK) :
    ∃ c₀ : MvPowerSeries σ Z, MvPowerSeries.map ι c₀ = c := by
  choose f hf using fun d => mem_range (h d)
  refine ⟨f, ?_⟩
  ext d
  exact (MvPowerSeries.coeff_map ι d (f : MvPowerSeries σ Z)).trans (hf d)
end Formalism.L2.Th1.A.CubeR
