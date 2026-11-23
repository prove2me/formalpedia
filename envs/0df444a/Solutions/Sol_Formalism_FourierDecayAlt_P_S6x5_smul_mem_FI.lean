-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.smul_mem_FI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:47.402409+00:00
-- url     : https://prove2.me/submissions/d6efa6ab-b3d1-4e42-a9d3-f11f7662ad28

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E)
    (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht
  rw [Algebra.smul_def] at this
  exact this
end Formalism.FourierDecayAlt.P.S6x5
