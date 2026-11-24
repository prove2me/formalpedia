-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.sv_dRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:29:27.793893+00:00
-- url     : https://prove2.me/submissions/959446c4-9ac5-432b-a73b-7c240132d1a9

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_ckOn_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_rdV_orbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_RdV


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
theorem _root_.solution (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) : SV σ (dRep σ X w) := by
  have h : CkOn ⊤ (GV k r) (RdV X (fun x => σ x w)) :=
    B5.ckOn_RdV (m := ⊤) hX (by rw [top_add]; exact hw)
  exact ckOn_congr (fun g hg => rdV_orbit hrep hw hX hg) h
end Formalism.FourierDecayAlt.P.Qb1
