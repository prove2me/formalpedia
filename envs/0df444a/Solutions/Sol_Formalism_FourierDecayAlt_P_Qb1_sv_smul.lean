-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.sv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:46:33.774897+00:00
-- url     : https://prove2.me/submissions/aa925a53-0528-4038-8cdb-3c6e2bcf39b4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_ckOn_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution {σ : Mx k r → (Vs →L[ℂ] Vs)} {w : Vs} (s : ℂ) (h : SV σ w) : SV σ (s • w) := by
  unfold SV at *
  have := ckOn_smul s h
  simpa only [map_smul] using this
end Formalism.FourierDecayAlt.P.Qb1
