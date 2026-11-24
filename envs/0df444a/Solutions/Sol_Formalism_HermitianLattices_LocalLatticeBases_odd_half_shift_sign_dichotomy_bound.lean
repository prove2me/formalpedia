-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.odd_half_shift_sign_dichotomy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:28.033842+00:00
-- url     : https://prove2.me/submissions/31b5323a-f408-4a1f-a150-66178e254c86

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
theorem _root_.solution : OddHalfShiftSignDichotomyBound := by
  intro t _ ht ε hε v W C N hv
  have ht' : (0:ℝ) ≤ t := by exact_mod_cast ht
  rcases hε with rfl | rfl
  · refine ⟨Or.inr (by push_cast; ring), ?_⟩
    push_cast
    rw [abs_le] at hv ⊢
    constructor <;> linarith [hv.1, hv.2]
  · refine ⟨Or.inl (by push_cast; ring), ?_⟩
    push_cast
    rw [abs_le] at hv ⊢
    constructor <;> linarith [hv.1, hv.2]
end Formalism.HermitianLattices.LocalLatticeBases
