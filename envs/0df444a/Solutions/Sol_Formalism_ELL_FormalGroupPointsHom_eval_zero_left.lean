-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.eval_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:10.491193+00:00
-- url     : https://prove2.me/submissions/67c0e94d-2596-403c-9c70-731d7e3bb17c

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_X1
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
theorem _root_.solution (F : FormalGroup K) (hF : IntegralMv F.toPowerSeries) {b : K}
    (hb : ‖b‖ < 1) : evalMv2 F.toPowerSeries 0 b = b := by
  have h := evalMv2_subst hF (s := 0) (t := MvPowerSeries.X 1) (fun d => by simp) (integral_X 1)
    (by simp) (by simp) (a := 0) (b := b) (by simp) hb
  rw [F.zero_add (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), evalMv2_X1, evalMv2_zero'] at h
  exact h.symm
end Formalism.ELL.FormalGroupPointsHom
