-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.uw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:25.191719+00:00
-- url     : https://prove2.me/submissions/9d6055be-1a68-4a19-9442-92011a7bb027

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_glev_mul
import Theorems.Thm_QnRdSkewW_glev_mul
import Theorems.Thm_QnYLeibnizW_glev_mul


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
open AnisotropicColumnSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SkewHermitianParts
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {g h : Mx k r} (hg : g ∈ UWset k r z) (hh : h ∈ UWset k r z) :
    g * h ∈ UWset k r z := by
  have := Qx8.glev_mul (Qx8.uw_glev (Fin.last r) hg) (Qx8.uw_glev (Fin.last r) hh)
  refine ⟨this.1, fun a => this.2 a (by simp), ?_⟩
  rw [← Matrix.mulVec_mulVec, hh.2.2, hg.2.2]
end Formalism.FourierDecayAlt.P.SkewHermitianParts
