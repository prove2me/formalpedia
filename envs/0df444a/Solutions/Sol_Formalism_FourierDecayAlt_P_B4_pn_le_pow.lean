-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.pn_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:13:44.887163+00:00
-- url     : https://prove2.me/submissions/4609c320-b358-45ee-8dc1-836c3c6c2ae6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_cons

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (w : List (Bool × Mat k r)) (K : ℝ) (h : ∀ x ∈ w, ‖x.2‖ ≤ K) :
    pn w ≤ K ^ w.length := by
  induction w with
  | nil => simp [pn]
  | cons x w ih =>
    rw [pn_cons, List.length_cons, pow_succ']
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    exact mul_le_mul hx ih' (pn_nonneg w) (le_trans (norm_nonneg _) hx)
end Formalism.FourierDecayAlt.P.B4
