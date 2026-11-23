-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.st_phase_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:17.382714+00:00
-- url     : https://prove2.me/submissions/e7acfa40-47e9-4307-80d8-8a3c3638d097

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_sLow_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_sLow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (h : Point K) (c : Kˣ) (ξ : Fin h.1.sum → K)
    (u : upUniG K (addBlock h 1 c).1.sum) (ψ : AddChar K ℂ) :
    phase ψ ((sec_lowJ h c 1 ξ, u) :
      lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum) =
      ψ (lastE ξ + sUp (sec_m u)) := by
  unfold phase
  change ψ (sLow (sec_m (sec_lowJ h c 1 ξ)) + sUp (sec_m u)) = _
  rw [sec_lowJ_m, sec_sLow]
  have h1 : sec_m (1 : lowW K h.1 h.2) = 1 := rfl
  rw [h1, st_sLow_one, Matrix.vecMul_one, zero_add]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
