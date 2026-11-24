-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dg_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:38.664798+00:00
-- url     : https://prove2.me/submissions/f60a4baa-6b2f-4ba9-89aa-f886f95070b5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (a : Fin r) (h : a.val + 1 < r) :
    dg k r t (eI k r a) * dg k r t⁻¹ (eI k r ⟨a.val + 1, h⟩) = (t : ℂ) := by
  have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
  simp only [dg, eI, Fin.is_lt, h, ↓reduceIte]
  rw [← Complex.ofReal_mul, e, pow_succ, inv_pow]
  congr 1
  rw [mul_comm (t ^ _) t, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), mul_one]
end Formalism.FourierDecayAlt.P.B4
