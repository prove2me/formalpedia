-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x1.smul_mem_FI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:07.478998+00:00
-- url     : https://prove2.me/submissions/6ac39a9c-461d-4dfe-9d79-741a4a5b2712

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x1
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x1
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E)
    (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht
  rw [Algebra.smul_def] at this
  exact this
end Formalism.FourierDecayAlt.P.S6x1
