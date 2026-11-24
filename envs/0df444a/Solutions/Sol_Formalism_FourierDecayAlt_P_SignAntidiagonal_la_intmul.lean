-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.la_intmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:20.665817+00:00
-- url     : https://prove2.me/submissions/e596b9ee-11da-4f5c-b35b-8086700f3f57

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthExpansionIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (La : A →ₗ[ℂ] M) (z : ℤ) (x : A) :
    La ((z : A) * x) = (z : ℂ) • La x := by
  have hz : ((z : A) * x) = (z : ℂ) • x := by
    rw [Algebra.smul_def, map_intCast]
  rw [hz, map_smul]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
