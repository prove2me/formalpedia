-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.function_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:42.603555+00:00
-- url     : https://prove2.me/submissions/4d8ad528-c678-4739-a3ae-3718b8d69932

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx1_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx1_vz_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.FnNonzero := by
  intro r v TT
  refine ⟨coord_ne r v, fun h => ?_⟩
  have he : (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1) : Expo r) ≠ 0 := by
    intro h0
    have := congrFun (congrArg ofLex h0) vz
    change ((Pi.single vz (1 : ℤ) + Pi.single vzb 1 : Var r → ℤ) vz) = (0 : Var r → ℤ) vz at this
    simp [Pi.single_apply, vz_ne (r := r)] at this
  have hc := congrArg (fun s : Fn r => s.coeff (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1))) h
  simp [gg, coord, HahnSeries.single_mul_single, HahnSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.coeff_single, he] at hc
end Formalism.FourierDecayAlt.P
