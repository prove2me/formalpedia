-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.ckOn_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:24.705187+00:00
-- url     : https://prove2.me/submissions/b362d091-c62f-4abe-aaed-95f1de25698c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

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
theorem _root_.solution {f : Mat k r → E} {m n : ℕ} (h : m ≤ n) (hf : CkOn ((n : ℕ) : ℕ∞) (GV k r) f) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  unfold CkOn at *
  intro g₀ hg
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg
  exact ⟨U, f', hU, hgU, hc.of_le (by exact_mod_cast h), he⟩
end Formalism.FourierDecayAlt.P.B4
