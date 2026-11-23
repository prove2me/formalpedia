-- Prove2me | solution 1 for Formalism.CountingSumsFrames.slTwoCommutator_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:27.81333+00:00
-- url     : https://prove2.me/submissions/f3e89960-6d90-443e-b26d-38dc3ce14e5f

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
import Theorems.Thm_Formalism_CountingSumsFrames_ctrF_h_mul
import Theorems.Thm_Formalism_CountingSumsFrames_eulX_of_mem
import Theorems.Thm_Formalism_CountingSumsFrames_eulY_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SlTwo := by
  intro K _ _ k A B f hf
  rw [ctrF_h_mul, eulX_of_mem hf, eulY_of_mem hf]
  simp only [Algebra.smul_def, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero, map_add, map_mul,
      map_one, map_zero, map_natCast]
  ring
end Formalism.CountingSumsFrames
