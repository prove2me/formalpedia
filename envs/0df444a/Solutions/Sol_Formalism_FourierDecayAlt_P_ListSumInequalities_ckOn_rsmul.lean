-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.ckOn_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:33:48.500173+00:00
-- url     : https://prove2.me/submissions/98aba9e7-d84f-4955-aef3-1379fcfa4df5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution {f : Mat k r → E} {m : ℕ∞} (a : ℝ) (hf : CkOn m (GV k r) f) :
    CkOn m (GV k r) (fun g => a • f g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', heq⟩ := hf g₀ hg₀
  exact ⟨U, fun g => a • f' g, hU, hgU, hf'.const_smul a, fun g hg hgv => by
    show a • f g = a • f' g
    rw [heq g hg hgv]⟩
end Formalism.FourierDecayAlt.P.ListSumInequalities
