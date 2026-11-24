-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:59.35904+00:00
-- url     : https://prove2.me/submissions/8871671c-b141-4b79-8eb8-a88c5f288196

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (v : ι → ℝ) :
    ∑ i, v i ^ 2 ≤ (Fintype.card ι + 1 : ℝ) * ‖v‖ ^ 2 := by
  have h1 : ∀ i, v i ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i
    have hi := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at hi
    nlinarith [abs_nonneg (v i), sq_abs (v i)]
  calc ∑ i, v i ^ 2 ≤ ∑ _i : ι, ‖v‖ ^ 2 := Finset.sum_le_sum (fun i _ => h1 i)
    _ = (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card ι + 1 : ℝ) * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
end Formalism.HermitianLatticesTheory
