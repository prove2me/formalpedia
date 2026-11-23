-- Prove2me | solution 1 for Formalism.ELL.PadicMultiplication.map_mulN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:09.905178+00:00
-- url     : https://prove2.me/submissions/827533d0-39b0-4980-a29f-78389a949802

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
import Theorems.Thm_Formalism_ELL_PadicMultiplication_mulN_succ
import Theorems.Thm_Formalism_ELL_PadicMultiplication_constantCoeff_mulN
import Theorems.Thm_Formalism_G_LogP_hs2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.ELL Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicMultiplication
theorem _root_.solution (F : FormalGroup (unitBall K)) (m : ℕ) :
    (mulN F (m + 1)).map (unitBall K).subtype =
      MvPowerSeries.subst
        (![(mulN F m).map (unitBall K).subtype, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
        (F.map (unitBall K).subtype).toPowerSeries := by
  rw [mulN_succ]
  have hs := hs2 (R := unitBall K) (constantCoeff_mulN F m)
    (u := mulN F m) (v := (PowerSeries.X : PowerSeries (unitBall K))) PowerSeries.constantCoeff_X
  rw [PowerSeries.map, MvPowerSeries.map_subst hs]
  simp only [FormalGroup.map_toPowerSeries]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact PowerSeries.map_X _
end Formalism.ELL.PadicMultiplication
