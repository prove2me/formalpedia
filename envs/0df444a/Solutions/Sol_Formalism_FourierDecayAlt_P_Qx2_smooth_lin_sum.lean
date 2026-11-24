-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.smooth_lin_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:54:04.249809+00:00
-- url     : https://prove2.me/submissions/18485df3-dbe2-46ff-95b0-cc7fc24220e2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (a : ℕ → ℂ) {c : ℕ → Mx k r → E} (hc : ∀ j, SmoothLev k r i D (c j)) (N : ℕ) :
    SmoothLev k r i D (fun y => ∑ j ∈ Finset.range N, a j • c j y) := by
  induction N with
  | zero =>
    simp only [Finset.sum_range_zero]
    exact smooth_zero
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    exact smooth_add ih (smooth_smul (hc N) (a N))
end Formalism.FourierDecayAlt.P.Qx2
