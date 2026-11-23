-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.length_average_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:02.486877+00:00
-- url     : https://prove2.me/submissions/630deb66-cae8-41e0-9786-35d2f8e5c4b5

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
theorem _root_.solution : LemmaB'_avg := by
  intro k n S mult hS hm hn j
  have key : ∀ i : Fin k, ∑ w ∈ S, mult w * w i = ∑ w ∈ S, mult w * w j := by
    intro i
    apply Finset.sum_nbij' (fun w => w ∘ Equiv.swap i j) (fun w => w ∘ Equiv.swap i j)
    · intro w hw; exact hS _ w hw
    · intro w hw; exact hS _ w hw
    · intro w _; funext a; simp [Function.comp]
    · intro w _; funext a; simp [Function.comp]
    · intro w _; simp [hm]
  have : ∑ i : Fin k, ∑ w ∈ S, mult w * w i = k * ∑ w ∈ S, mult w * w j := by
    rw [Finset.sum_congr rfl (fun i _ => key i)]; simp
  rw [← this, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.mul_sum, hn w hw, mul_comm]
end Formalism.HermitianLattices.LocalLatticeBases
