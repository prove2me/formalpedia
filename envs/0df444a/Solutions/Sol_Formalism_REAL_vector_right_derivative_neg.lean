-- Prove2me | solution 1 for Formalism.REAL.vector_right_derivative_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:00:02.663656+00:00
-- url     : https://prove2.me/submissions/2a3fa53f-f5d2-4c47-8214-a076fd0e77ce

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.REAL
theorem _root_.solution (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnGV ε f) (hB : inG ε B) (hg : inUJ ε g) :
    RdV (-B) f g = -RdV B f g := by
  have h2 := (hl n ε E f f B B (-1) 0 g hf hf hB hB hg).2.1
  simpa using h2
end Formalism.REAL
