-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.skew_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:32:56.156889+00:00
-- url     : https://prove2.me/submissions/a4fc9efa-6904-4b84-b14d-0d743f4ea0ad

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {j : ℕ} (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by
  unfold skewOf
  rw [conjTranspose_add, conjTranspose_sub, conjTranspose_conjTranspose, diagonal_conjTranspose]
  have : (star fun i => Complex.I * ((q.2 i : ℝ) : ℂ)) = -(fun i => Complex.I * ((q.2 i : ℝ) : ℂ)) := by
    funext i
    simp [Complex.conj_ofReal]
  have hd : diagonal (-(fun i => Complex.I * ((q.2 i : ℝ) : ℂ))) =
      -diagonal (fun i => Complex.I * ((q.2 i : ℝ) : ℂ)) := by
    ext a b
    simp only [diagonal_apply, Matrix.neg_apply]
    split_ifs <;> simp
  rw [this, hd]
  abel
end Formalism.FourierDecayAlt.P.Ux5
