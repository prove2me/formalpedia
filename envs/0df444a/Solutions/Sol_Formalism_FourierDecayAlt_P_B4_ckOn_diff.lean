-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.ckOn_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:03:15.801211+00:00
-- url     : https://prove2.me/submissions/bae5a71c-e3f0-40bf-b3dd-ee3a8ad321de

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hasDerivAt_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cast_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {f : Mat k r → E} {X g : Mat k r} (m : ℕ) (b : Bool)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) (hX : inLie k r X) (hg : g ∈ GV k r) :
    DifferentiableAt ℝ (fun t : ℝ => f (cv b X t g)) 0 := by
  unfold CkOn at hf
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hc.contDiffAt (hU.mem_nhds hgU)).differentiableAt (cast_ne_zero m)
  exact (hasDerivAt_ext b hU hgU hg hd hff hX).differentiableAt
end Formalism.FourierDecayAlt.P.B4
