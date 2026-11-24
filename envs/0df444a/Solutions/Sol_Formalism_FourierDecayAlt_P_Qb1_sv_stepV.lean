-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.sv_stepV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:07:08.710441+00:00
-- url     : https://prove2.me/submissions/468eb783-4e9e-4531-bd33-ea7cb583469a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_ecRep

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
theorem _root_.solution (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (c : ℂ) (a b : Fin (2 * r + k + 1)) :
    SV σ (stepV σ c a b w) := by
  unfold stepV
  refine sv_add ?_ (sv_ecRep hrep hw _)
  split_ifs
  · exact sv_smul c hw
  · exact sv_zero σ
end Formalism.FourierDecayAlt.P.Qb1
