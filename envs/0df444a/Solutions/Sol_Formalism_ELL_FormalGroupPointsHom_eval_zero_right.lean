-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.eval_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:11.184979+00:00
-- url     : https://prove2.me/submissions/8d6b015f-7855-42d0-b890-8d72715fedd2

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_X0
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_subst
import Theorems.Thm_P2M_Formalism_ELL_FormalGroupPointsHom_evalMv2_zero__d743f55ca61b
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_X

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution (F : FormalGroup K) (hF : IntegralMv F.toPowerSeries) {a : K}
    (ha : ‖a‖ < 1) : evalMv2 F.toPowerSeries a 0 = a := by
  have h := evalMv2_subst hF (s := MvPowerSeries.X 0) (t := 0) (integral_X 0) (fun d => by simp)
    (by simp) (by simp) (a := a) (b := 0) ha (by simp)
  rw [F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), evalMv2_X0, evalMv2_zero'] at h
  exact h.symm
end Formalism.ELL.FormalGroupPointsHom
