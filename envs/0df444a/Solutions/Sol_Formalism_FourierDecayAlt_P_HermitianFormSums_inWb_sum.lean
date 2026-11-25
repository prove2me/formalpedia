-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormSums.inWb_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:39:39.028974+00:00
-- url     : https://prove2.me/submissions/35d700ec-3bb5-47c3-b8c2-42938874120a

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.HermitianFormSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianFormSums
theorem _root_.solution {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ a, inWb k r (v a)) : inWb k r (∑ a ∈ s, c a • v a) := by
  intro i hi
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [Pi.smul_apply, hv a i hi, smul_zero]
end Formalism.FourierDecayAlt.P.HermitianFormSums
