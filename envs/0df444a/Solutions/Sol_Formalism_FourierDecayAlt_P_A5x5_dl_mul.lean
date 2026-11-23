-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.dl_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:42.648312+00:00
-- url     : https://prove2.me/submissions/2b54dbe1-e76a-4fde-94c2-665d625bc955

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_map_mv_mul
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
theorem _root_.solution (hL : Lat (LL R ι)) {M N : Matrix ι ι K} (hM : IsUnit M.det) (hN : IsUnit N.det) :
    dl R (M * N) = dl R M * dl R N := by
  unfold dl
  rw [map_mv_mul, ← gi_trans (lat_map hM (lat_map hN hL)) (lat_map hM hL) hL,
    gi_map (mv_injective hM), mul_comm]
end Formalism.FourierDecayAlt.P.A5x5
