-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.orthogonal_lattice_properties
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:28.482053+00:00
-- url     : https://prove2.me/submissions/0bd4fbd8-b4c2-4e34-bbac-4f44714cbd56

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_lat

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
theorem _root_.solution : Formalism.FourierDecayAlt.A6.PerpLat := by
  intro K _ _ _ R ψ hd hn L hL
  obtain ⟨h1, h2, h3⟩ := perp_lat hd hn (lat_iff.1 hL)
  exact ⟨lat_iff.2 h1, h2, h3⟩
end Formalism.FourierDecayAlt.P
