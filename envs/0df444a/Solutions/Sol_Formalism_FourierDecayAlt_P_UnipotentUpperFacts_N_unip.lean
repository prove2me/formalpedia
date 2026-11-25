-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:25.501158+00:00
-- url     : https://prove2.me/submissions/4eff6572-c494-49d8-908f-436b99de8700

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_N_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_strict_pow_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentUpperFacts
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.UnipotentUpperFacts
theorem _root_.solution {g : B.Mat k r} (hg : g ∈ Nset k r) : (g - 1) ^ (2 * r + k + 1) = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, N_upper hg i j hji, Matrix.one_apply, sub_self]
end Formalism.FourierDecayAlt.P.UnipotentUpperFacts
