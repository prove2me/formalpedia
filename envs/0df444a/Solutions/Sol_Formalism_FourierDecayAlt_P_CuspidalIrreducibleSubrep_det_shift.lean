-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.det_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:44.684699+00:00
-- url     : https://prove2.me/submissions/4ff9f1ba-b3b9-4c6f-abb0-167ed60498b7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep

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
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := by
  rw [Matrix.det_of_upperTriangular]
  · simp [hX _ _ le_rfl]
  · intro i j hij
    have hne : i ≠ j := (ne_of_lt hij).symm
    simp [Matrix.one_apply_ne hne, hX i j hij.le]
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
