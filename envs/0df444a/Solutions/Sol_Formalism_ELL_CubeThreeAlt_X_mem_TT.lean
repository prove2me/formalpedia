-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.X_mem_TT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:26.702688+00:00
-- url     : https://prove2.me/submissions/a24df45a-f877-4242-adbc-38af0faeee5d

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_mem_TT

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
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ∈ TT W σ := by
  classical
  rw [mem_TT]
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _
end Formalism.ELL.CubeThreeAlt
