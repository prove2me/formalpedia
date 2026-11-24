-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.upper_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:25:19.805562+00:00
-- url     : https://prove2.me/submissions/5fc1ca36-a712-41a7-8099-84dc5d7657b4

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {u : Matrix (Fin p) (Fin p) ℂ} (hu : uniK (kU p) u) : u = G.upper (fun q => u q.1.1 q.1.2) := by
  ext a b
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply]
  rcases lt_trichotomy a b with h | h | h
  · simp [h, ne_of_lt h]
  · subst h; simp [hu.1]
  · simp [not_lt.mpr h.le, ne_of_gt h, hu.2 a b (kU_lt.mpr h)]
end Formalism.FourierDecayAlt.P.Ux2
