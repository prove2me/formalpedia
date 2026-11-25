-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.capelli_two_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:02:21.439808+00:00
-- url     : https://prove2.me/submissions/2afa0ed4-1b12-47f1-b484-f14ae61ffe2a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_polyAt_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_polyAt_sum
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_qminor_poly__0e6aae111771

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
theorem _root_.solution (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) (s : ℂ) :
    PolyAt (mdim k r i - 1) (fun Y => chat2L (EH k r) (posL k r i) (Y + s) a a' β β' f x) := by
  simp only [chat2L]
  refine polyAt_sum _ _ fun p _ => polyAt_sum _ _ fun p' _ => polyAt_sum _ _ fun q _ =>
    polyAt_sum _ _ fun q' _ => ?_
  by_cases hc : p < p' ∧ q < q'
  · simp only [if_pos hc]
    have h1 : p.val < p'.val := hc.1
    have h2 := p'.isLt
    have hm : mdim k r i - 2 + 1 = mdim k r i - 1 := by omega
    rw [← hm]
    exact (qminor_poly' hD hf hx (skip2 p p') (skip2 q q') s).smul _
  · simp only [if_neg hc]
    exact polyAt_zero _
end Formalism.FourierDecayAlt.P.Qx2
