-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.primitive_orbit_functional_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:28.504061+00:00
-- url     : https://prove2.me/submissions/59b76c55-8ba0-456c-945d-9740ce3158ce

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : PrimitiveOrbitFunctionalUnique := by
  intro F _ n f g e he
  constructor
  · rintro ⟨h1, h2⟩
    funext j
    have := h1 (Pi.single j 1 - f j • e) (by simp [dotProduct_sub, he])
    simp [dotProduct_sub, h2] at this
    exact (sub_eq_zero.mp this)
  · rintro rfl
    exact ⟨fun _ h => h, he⟩
end Formalism.HermitianLattices.LocalLatticeBases
