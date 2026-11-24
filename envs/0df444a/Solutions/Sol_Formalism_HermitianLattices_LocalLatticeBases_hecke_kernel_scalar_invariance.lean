-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.hecke_kernel_scalar_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:45.366212+00:00
-- url     : https://prove2.me/submissions/0dc05ebf-1af1-4ee7-a254-349590c4ebf6

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
theorem _root_.solution : HeckeKernelScalarInvariance := by
  intro q _ n n' w ph c fW
  simp [kerK, Matrix.smul_vecMul]
end Formalism.HermitianLattices.LocalLatticeBases
