-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.wMat_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:53:52.357812+00:00
-- url     : https://prove2.me/submissions/1196845d-34e6-4a32-8ac6-e9400816ec42

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
theorem _root_.solution (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext i j
  simp only [G.wMat, mul_apply, of_apply, one_apply]
  rw [Finset.sum_eq_single i.rev (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Fin.rev_rev]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]
end Formalism.FourierDecayAlt.P.Ux5
