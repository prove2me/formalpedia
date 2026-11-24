-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.ckOn_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:49.279264+00:00
-- url     : https://prove2.me/submissions/c244bf23-01a4-4d37-90a7-3508cd0a5825

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B4_op__contDiffOn_a13b807b4df6
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B4_op_eq_op__514f38137870

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
theorem _root_.solution {f : Mat k r → E} {X : Mat k r} (m : ℕ) (b : Bool)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) (hX : inLie k r X) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) (op b X f) := by
  unfold CkOn at *
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, op' b X f', hU, hgU, op'_contDiffOn m b X hU hc,
    fun g hg hgG => op_eq_op' m b hU hc hff hX g hg hgG⟩
end Formalism.FourierDecayAlt.P.B4
