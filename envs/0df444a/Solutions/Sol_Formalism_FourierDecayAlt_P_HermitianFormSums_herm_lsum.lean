-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormSums.herm_lsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:22.693535+00:00
-- url     : https://prove2.me/submissions/e1bbf192-010e-4713-8246-d0ad8b73dfda

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_add_left__13aa38a1a87a
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_smul_left__bcf36eb50b87


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
namespace Formalism.FourierDecayAlt.P.HermitianFormSums
theorem _root_.solution {N : ℕ} {ι : Type*} (H : Matrix (Fin N) (Fin N) ℂ) (s : Finset ι) (c : ι → ℂ) (v : ι → Fin N → ℂ)
    (w : Fin N → ℂ) : herm H (∑ a ∈ s, c a • v a) w = ∑ a ∈ s, c a * herm H (v a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Qx8.herm_add_left', Qx8.herm_smul_left', ih]
end Formalism.FourierDecayAlt.P.HermitianFormSums
