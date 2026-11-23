-- Prove2me | solution 1 for Formalism.DivisionValues.W5.anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:45.852483+00:00
-- url     : https://prove2.me/submissions/91772e57-3b65-4c82-9454-08fc396a0a22

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_exp_two_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.W5
namespace Formalism.DivisionValues.W5
theorem _root_.solution (u v : ℝ) (hu : 8 ≤ u) (huv : u ≤ v) :
    Real.log v / v ^ 2 ≤ Real.log u / u ^ 2 := by
  have hA := Real.log_div_self_rpow_antitoneOn (a := 2) (by norm_num)
  have he : Real.exp (2 : ℝ)⁻¹ ≤ 8 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_two_le
    norm_num
  have := hA (a := u) (b := v) (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) huv
  simpa [Real.rpow_two] using this
end Formalism.DivisionValues.W5
