-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.linearCoeff_one_formal_group_law
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:43.523149+00:00
-- url     : https://prove2.me/submissions/0aea415b-c1cc-4bde-9b15-46d672426a4e

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_ccd_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution (F : FormalGroup (Formalism.G.unitBall K)) : ccd 1 (FK F).toPowerSeries = 1 := by
  rw [ccd_single]
  simp [Formalism.ELL.FK, FormalGroup.map, MvPowerSeries.coeff_map, F.lin_coeff_Y]
end Formalism.ELL.FormalGroupQuadraticJets
