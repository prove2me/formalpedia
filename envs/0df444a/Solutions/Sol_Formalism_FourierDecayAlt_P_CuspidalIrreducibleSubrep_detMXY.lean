-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.detMXY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:09.504803+00:00
-- url     : https://prove2.me/submissions/fbfcc49a-d734-40a3-946c-83ea4b1d744f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_det_Mcoord
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_cornerSplit
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_isStrictUpper_strictUpper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
theorem _root_.solution : DetMXY := by
  intro m D t p hC
  have hX := isStrictUpper_strictUpper (redOf m p).2.2.1
  have h := det_Mcoord t (strictUpper (redOf m p).2.2.1) hX (redOf m p).2.2.2
    (Fin.cons (rhoXY m D t p) (redOf m p).2.1) (redOf m p).1
  rw [cornerSplit m _ _ _ _ t] at h
  have e : detM (MXY m D t p) = (Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
      (Fin.cons (rhoXY m D t p) (redOf m p).2.1) (redOf m p).1).det := rfl
  rw [e, h]
  congr 1
  have hC' : Cof (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 t ≠ 0 := hC
  rw [rhoXY, rho1, mul_div_cancel₀ _ hC']
  ring
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
