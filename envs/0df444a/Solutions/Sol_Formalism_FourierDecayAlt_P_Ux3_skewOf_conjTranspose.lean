-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.skewOf_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:31:04.885332+00:00
-- url     : https://prove2.me/submissions/0ca2211d-25fa-4046-98e5-e0d27deefee4

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul

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
theorem _root_.solution {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) : (skewOf q)ᴴ = -skewOf q := by
  ext a b
  simp only [skewOf, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    star_add, star_sub, star_star, Matrix.diagonal_apply]
  by_cases h : b = a
  · subst h
    simp [Complex.conj_ofReal]
    try ring
  · simp [h, Ne.symm h]
    try ring
end Formalism.FourierDecayAlt.P.Ux3
