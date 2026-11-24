-- Prove2me | solution 1 for Formalism.REAL.vector_right_derivative_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:00:01.073498+00:00
-- url     : https://prove2.me/submissions/875fe97d-ecb2-4c35-9f82-3d02935ae7f7

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
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnGV ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : RdV (A + B) f g = RdV A f g + RdV B f g := (hl n ε E f f A B 0 0 g hf hf hA hB hg).1
end Formalism.REAL
