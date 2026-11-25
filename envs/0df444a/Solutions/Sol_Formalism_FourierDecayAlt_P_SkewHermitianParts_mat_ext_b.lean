-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.mat_ext_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:14:58.155903+00:00
-- url     : https://prove2.me/submissions/7bfffb07-a1ac-4bbb-8f60-8da467ab416d

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_mulVec_bvec
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_mulVec_bvec
import Theorems.Thm_PI_IsotropicReflections_mulVec_bvec


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
theorem _root_.solution {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℂ} (h : ∀ p, M *ᵥ bvec p = N *ᵥ bvec p) : M = N := by
  ext i j
  rw [← Qx8.mulVec_bvec M, h, Qx8.mulVec_bvec]
end Formalism.FourierDecayAlt.P.SkewHermitianParts
