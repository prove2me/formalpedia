-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_coercive_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:30.764335+00:00
-- url     : https://prove2.me/submissions/ee147c12-f6a9-4a51-a56c-cf3f00b4dd7d

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_sq_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_coercive
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_castform

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
theorem _root_.solution (G : Matrix ι ι ℚ)
    (hG : ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w)) :
    ∃ l : ℝ, 0 < l ∧ ∀ w : ι → ℚ, l * ∑ i, ((w i : ℚ) : ℝ) ^ 2 ≤ ((w ⬝ᵥ (G *ᵥ w) : ℚ) : ℝ) := by
  obtain ⟨l, hl, hcoer⟩ := thetaSummable_coercive G hG
  have hN : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  refine ⟨l / (2 * (Fintype.card ι + 1)), by positivity, fun w => ?_⟩
  have h1 := hcoer (fun i => (w i : ℝ))
  rw [thetaSummable_castform] at h1
  have h2 := thetaSummable_sq_le (fun i => (w i : ℝ))
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hl.le, mul_le_mul_of_nonneg_left h1 hN.le]
end Formalism.HermitianLatticesTheory
