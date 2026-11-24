-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.hasDerivAt_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:38.227029+00:00
-- url     : https://prove2.me/submissions/d8cd46d1-23c5-41c4-804f-e95c0184fe60

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_one_mem_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_rdV_hasDerivAt
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
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) w) (σ g (dRep σ X w)) 0 := by
  have h1 := B5.rdV_hasDerivAt (B5.ckOn_mono (m := 1) le_top hw) (one_mem_GV (k := k) (r := r)) hX
  simp only [Matrix.one_mul] at h1
  have hd : dRep σ X w = RdV X (fun g => σ g w) 1 := h1.deriv
  rw [hd]
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 g hg _ (B5.exp_mem hX t)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', this,
    ContinuousLinearMap.comp_apply]
end Formalism.FourierDecayAlt.P.Qb1
