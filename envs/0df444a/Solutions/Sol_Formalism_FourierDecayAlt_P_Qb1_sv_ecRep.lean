-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.sv_ecRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:42.131462+00:00
-- url     : https://prove2.me/submissions/95bb6aef-be84-4615-966f-2fc57101b95a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_dRep
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_lie1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_lie2

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
theorem _root_.solution (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (Z : Mx k r) :
    SV σ (EcRep (Hpk k r) σ Z w) :=
  sv_add (sv_dRep hrep hw (lie1 Z)) (sv_smul _ (sv_dRep hrep hw (lie2 Z)))
end Formalism.FourierDecayAlt.P.Qb1
