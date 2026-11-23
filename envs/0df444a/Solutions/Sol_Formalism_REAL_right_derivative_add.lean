-- Prove2me | solution 1 for Formalism.REAL.right_derivative_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:18.846153+00:00
-- url     : https://prove2.me/submissions/b55ad9f4-341e-43bd-b210-75a6159589f1

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A + B) f g = Rd A f g + Rd B f g :=
  (hl n ε f f A B 0 0 g hf hf hA hB hg).1
end Formalism.REAL
