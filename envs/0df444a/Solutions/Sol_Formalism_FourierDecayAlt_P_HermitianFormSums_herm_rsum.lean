-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormSums.herm_rsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:26:41.197893+00:00
-- url     : https://prove2.me/submissions/f18adfd5-ded3-4902-8e48-17ae355fdaf2

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_add_right__6879cf36a61e
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_smul_right__34189a3fdce0


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
    (w : Fin N → ℂ) : herm H w (∑ a ∈ s, c a • v a) = ∑ a ∈ s, star (c a) * herm H w (v a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Qx8.herm_add_right', Qx8.herm_smul_right', ih]
end Formalism.FourierDecayAlt.P.HermitianFormSums
