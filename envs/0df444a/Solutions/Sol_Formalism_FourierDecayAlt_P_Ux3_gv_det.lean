-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.gv_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:24:21.184774+00:00
-- url     : https://prove2.me/submissions/e3851227-50e2-4bd1-857f-33620b115013

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_isUnit_of_mul_self
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
theorem _root_.solution {r : ℕ} {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) : IsUnit γ.det := by
  have h : γᴴ * Hpk k r * γ = Hpk k r := hγ
  have hH : IsUnit (Hpk k r).det := isUnit_of_mul_self _ (hpk_sq k r)
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h3 : IsUnit ((γᴴ).det * (Hpk k r).det * γ.det) := by
    rw [h2]
    exact hH
  exact isUnit_of_mul_isUnit_right h3
end Formalism.FourierDecayAlt.P.Ux3
