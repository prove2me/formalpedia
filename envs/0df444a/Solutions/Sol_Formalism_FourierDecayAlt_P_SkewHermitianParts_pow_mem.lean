-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:59.210009+00:00
-- url     : https://prove2.me/submissions/296ce566-d7fb-494c-8ccd-7df3809cdd38

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Rep_zero


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
open Formalism.FourierDecayAlt.P.SkewHermitianParts
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
namespace Formalism.FourierDecayAlt.P.SkewHermitianParts
theorem _root_.solution (S : Submodule ℂ W) {A : W →L[ℂ] W} (hA : ∀ v ∈ S, A v ∈ S) (n : ℕ) : ∀ v ∈ S, (A ^ n) v ∈ S := by
  induction n with
  | zero => intro v hv; simpa using hv
  | succ n ih =>
    intro v hv
    rw [pow_succ]
    exact ih _ (hA v hv)
end Formalism.FourierDecayAlt.P.SkewHermitianParts
