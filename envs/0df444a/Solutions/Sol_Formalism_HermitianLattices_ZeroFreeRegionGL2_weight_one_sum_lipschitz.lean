-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.weight_one_sum_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:18.916896+00:00
-- url     : https://prove2.me/submissions/5a46faac-e4ff-4744-8d4e-4227b2d86d1a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_weighted_von_mangoldt_sum_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : WeightedSumLipschitzTrivial := by
  intro a w w' ha hw hww
  have hw' : 0 < w' := lt_of_lt_of_le hw hww
  have hfl : ⌊a / w'⌋₊ ≤ ⌊a / w⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_left ha.le hw hww)
  unfold G1
  have e1 := weighted_von_mangoldt_sum_identity a w' ⌊a / w⌋₊ ha hw' hfl
  have e2 := weighted_von_mangoldt_sum_identity a w ⌊a / w⌋₊ ha hw le_rfl
  have hpsi : Chebyshev.psi (a / w) = ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n := by
    unfold Chebyshev.psi; rfl
  have hS : |(∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * max (a / n - w') 0) - ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * max (a / n - w) 0|
      ≤ Chebyshev.psi (a / w) * (w' - w) := by
    rw [← Finset.sum_sub_distrib, hpsi, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
    apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
    refine (abs_max_sub_max_le_abs (a / n - w') (a / n - w) 0).trans ?_
    rw [show a / n - w' - (a / n - w) = -(w' - w) by ring, abs_neg, abs_of_nonneg (by linarith)]
  have hlog : |a * (Real.log (a / w) - Real.log (a / w'))| ≤ a / w * (w' - w) := by
    rw [Real.log_div ha.ne' hw.ne', Real.log_div ha.ne' hw'.ne']
    have h0 : 0 ≤ Real.log w' - Real.log w := sub_nonneg.2 (Real.log_le_log hw hww)
    have h1 : Real.log w' - Real.log w ≤ (w' - w) / w := by
      rw [← Real.log_div hw'.ne' hw.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hw' hw)
      have e : w' / w - 1 = (w' - w) / w := by field_simp
      linarith
    rw [show Real.log a - Real.log w - (Real.log a - Real.log w') = Real.log w' - Real.log w by ring,
      abs_of_nonneg (mul_nonneg ha.le h0)]
    calc a * (Real.log w' - Real.log w) ≤ a * ((w' - w) / w) := mul_le_mul_of_nonneg_left h1 ha.le
      _ = a / w * (w' - w) := by ring
  have hmain : w' * ((∑ n ∈ Icc 1 ⌊a / w'⌋₊, Λ n * (a / w' / n - 1)) - a / w' * (Real.log (a / w') - 1 - Real.eulerMascheroniConstant))
      - w * ((∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * (a / w / n - 1)) - a / w * (Real.log (a / w) - 1 - Real.eulerMascheroniConstant))
      = ((∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * max (a / n - w') 0) - ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * max (a / n - w) 0)
        + a * (Real.log (a / w) - Real.log (a / w')) := by
    rw [← e1, ← e2]; field_simp; ring
  rw [hmain, add_mul]
  exact (abs_add_le _ _).trans (add_le_add hS hlog)
end Formalism.HermitianLattices.ZeroFreeRegionGL2
