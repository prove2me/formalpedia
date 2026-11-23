-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.cof_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:21.974018+00:00
-- url     : https://prove2.me/submissions/88725407-0430-41f8-adfd-d95de6fc5a84

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_pow_apply_strict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    Cof X (Pi.single 0 1) t = t ^ m := by
  have hX' : IsStrictUpper (-X) := fun i j h => by simp [hX i j h]
  unfold Cof
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [Matrix.mulVec_single_one, Matrix.col_apply,
      pow_apply_strict (-X) hX' j 0 0 (by simpa using Nat.pos_of_ne_zero hj), zero_mul]
  · simp
end Formalism.FourierDecayAlt.P.G7
