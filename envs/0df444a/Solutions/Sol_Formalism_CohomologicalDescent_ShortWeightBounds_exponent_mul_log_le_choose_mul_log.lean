-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.exponent_mul_log_le_choose_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:18.995913+00:00
-- url     : https://prove2.me/submissions/d2effddb-14e5-463d-8325-5fdb576df721

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution (N l w e : ℕ) (y : ℝ) (he : e ≤ N.choose 2 * Nat.log l w) (hy : (w : ℝ) ≤ y)
    (hy1 : 1 ≤ y) : (e : ℝ) * Real.log l ≤ (N.choose 2 : ℝ) * Real.log y := by
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy1
  rcases Nat.lt_or_ge l 2 with hl | hl
  · have h0l : Real.log (l : ℝ) = 0 := by
      interval_cases l <;> simp
    rw [h0l, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hlogy
  · have key : ((Nat.log l w : ℕ) : ℝ) * Real.log l ≤ Real.log y := by
      rcases Nat.eq_zero_or_pos w with hw | hw
      · simp [hw, hlogy]
      · have hpow : l ^ Nat.log l w ≤ w := Nat.pow_log_le_self l hw.ne'
        have h1 : ((l ^ Nat.log l w : ℕ) : ℝ) ≤ y := le_trans (by exact_mod_cast hpow) hy
        have hpos : (0 : ℝ) < ((l ^ Nat.log l w : ℕ) : ℝ) := by
          have : 0 < l ^ Nat.log l w := pow_pos (by omega) _
          exact_mod_cast this
        calc ((Nat.log l w : ℕ) : ℝ) * Real.log l
            = Real.log (((l ^ Nat.log l w : ℕ) : ℝ)) := by rw [Nat.cast_pow, Real.log_pow]
          _ ≤ Real.log y := Real.log_le_log hpos h1
    have hlogl : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ l))
    calc (e : ℝ) * Real.log l ≤ ((N.choose 2 * Nat.log l w : ℕ) : ℝ) * Real.log l :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast he) hlogl
      _ = (N.choose 2 : ℝ) * (((Nat.log l w : ℕ) : ℝ) * Real.log l) := by push_cast; ring
      _ ≤ (N.choose 2 : ℝ) * Real.log y := mul_le_mul_of_nonneg_left key (by positivity)
end Formalism.CohomologicalDescent.ShortWeightBounds
