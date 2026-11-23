-- Prove2me | solution 1 for Formalism.FX.rectRes_sum_combo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:06.102644+00:00
-- url     : https://prove2.me/submissions/12932410-81be-48e9-8fcd-44e77f1ec139

import Definitions.Def_Formalism_LFunctionBounds_ExpSumLowerBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.FX
namespace Formalism.FX
theorem _root_.solution (P : Finset ℂ) (b A B C D : ℂ → ℂ) :
    ∑ p ∈ P, b p * (A p - B p + I * C p - I * D p) =
      ∑ p ∈ P, b p * A p - ∑ p ∈ P, b p * B p + I * ∑ p ∈ P, b p * C p - I * ∑ p ∈ P, b p * D p := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring
end Formalism.FX
