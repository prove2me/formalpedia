-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.volL_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:42.616606+00:00
-- url     : https://prove2.me/submissions/71cff212-5800-41fb-b28e-c60a1f2f555e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mulLeft_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution {R : Subring K} (hR : Lat R.toAddSubgroup) (b : Kˣ) {L : AddSubgroup K}
    (hL : Lat L) : volL R (mulLat (b : K) L) = modK R (b : K) * volL R L := by
  have hbR : Lat (mulR R (b : K)) := lat_mulLat b hR
  rw [volL_eq, volL_eq, modK_eq, ← gi_trans (lat_mulLat b hL) hbR hR, mul_comm]
  congr 1
  exact gi_map (mulLeft_injective b) L R.toAddSubgroup
end Formalism.FourierDecayAlt.P.A6x3
