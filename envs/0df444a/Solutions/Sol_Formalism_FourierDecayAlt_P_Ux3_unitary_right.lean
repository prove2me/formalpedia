-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.unitary_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:31:13.288825+00:00
-- url     : https://prove2.me/submissions/ac5967f5-13f0-4927-b21c-ae685397119d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution {r : ℕ} (g : B.Mat k r) (h : gᴴ * Hpk k r * g = Hpk k r) : g * Hpk k r * gᴴ = Hpk k r := by
  have h1 : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, hpk_sq]
  have h2 : g * (Hpk k r * gᴴ * Hpk k r) = 1 := by
    rw [← Matrix.inv_eq_left_inv h1]
    exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h1)
  calc g * Hpk k r * gᴴ = g * (Hpk k r * gᴴ * Hpk k r) * Hpk k r := by
        simp only [Matrix.mul_assoc, hpk_sq, Matrix.mul_one]
    _ = Hpk k r := by rw [h2, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Ux3
