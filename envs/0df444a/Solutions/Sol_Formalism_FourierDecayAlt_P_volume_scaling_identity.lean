-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.volume_scaling_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:30.493248+00:00
-- url     : https://prove2.me/submissions/f4597607-adf8-448e-82bd-aadbd2f6c2d6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_R


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.VolScale := by
  intro K _ _ _ R ψ hd b L hL
  exact ⟨lat_iff.2 (lat_mulLat b (lat_iff.1 hL)),
    volL_mulLat (lat_R hd.isOpen hd.isCompact) b (lat_iff.1 hL)⟩
end Formalism.FourierDecayAlt.P
