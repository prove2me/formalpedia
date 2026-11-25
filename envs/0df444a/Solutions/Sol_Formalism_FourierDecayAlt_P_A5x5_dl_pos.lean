-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.dl_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:06.422384+00:00
-- url     : https://prove2.me/submissions/f2f55fe2-4f62-469c-abe6-25150a99d67c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (hL : Lat (LL R ι)) {M : Matrix ι ι K} (hM : IsUnit M.det) : 0 < dl R M := by
  unfold dl
  exact gi_pos (lat_map hM hL) hL
end Formalism.FourierDecayAlt.P.A5x5
