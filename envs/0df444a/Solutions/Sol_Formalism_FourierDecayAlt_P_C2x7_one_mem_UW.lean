-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x7.one_mem_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:41.157865+00:00
-- url     : https://prove2.me/submissions/9b430e96-52a5-44d8-bdbf-c629b006eba6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x7
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x7
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z :=
  ⟨WeylGroupFacts.uh_one, fun a => ⟨by simp, by simp⟩, by simp⟩
end Formalism.FourierDecayAlt.P.C2x7
