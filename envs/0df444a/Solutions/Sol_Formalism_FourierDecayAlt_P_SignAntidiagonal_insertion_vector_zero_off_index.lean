-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.insertion_vector_zero_off_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:59:39.702998+00:00
-- url     : https://prove2.me/submissions/574c04ba-4aef-47be-95ba-6567a31b3fa4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k : ℕ}
variable (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (p : Fin (2 * (m + 1) + k + 1)) (hp : m + 1 ≤ p.val) (hne : p ≠ esI k (m + 1) i) : ViF m i Vc p = 0 := by
  unfold ViF; rw [if_neg hne, dif_neg (by omega)]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
