-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.lie1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:14:28.809008+00:00
-- url     : https://prove2.me/submissions/143fbfeb-a62b-4d3e-8d02-df52aa96e897

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart1_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution (Z : Mx k r) : inLie k r (hpart1 (Hpk k r) Z) := Qx2.hpart1_lie Z
end Formalism.FourierDecayAlt.P.Qb1
