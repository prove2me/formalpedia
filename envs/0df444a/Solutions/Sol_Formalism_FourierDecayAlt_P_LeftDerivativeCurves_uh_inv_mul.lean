-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.uh_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:26.084848+00:00
-- url     : https://prove2.me/submissions/7bd44310-20c8-46e9-9e6d-297883e4c886

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := by
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg,
      Qx2.hpk_sq']
  rw [Matrix.inv_eq_left_inv hl, hl]
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
