-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.linearCoeff_thirdParam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:18.4742+00:00
-- url     : https://prove2.me/submissions/eea8a75c-a54b-49bf-86f6-398d1d0ac13d

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_X
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_chordCoeffQuadratic
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_linearCoeff_chordCoeffQuadratic

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
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (hw : WFixed W w) (i : Fin 2) : (L i) (z3 W w) = -1 := by
  rw [z3, map_sub, map_sub, map_neg, L_mul, constantCoeff_chordCoeffQuadratic hw,
    linearCoeff_chordCoeffQuadratic hw, L_X, L_X]
  fin_cases i <;> simp
end Formalism.ELL.WeierstrassChordSeries
