-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_sum_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:05.415124+00:00
-- url     : https://prove2.me/submissions/bafb56d5-c686-4b52-aea7-2be66282890d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_weighted_sum_identity

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
theorem _root_.solution : WGLipschitz := by
  intro q _ χ a w w' ha hw hww
  have hw' : 0 < w' := lt_of_lt_of_le hw hww
  have hW : WGIdentity := weighted_sum_identity
  have hfl : ⌊a / w'⌋₊ ≤ ⌊a / w⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_left ha.le hw hww)
  rw [hW q χ a w' ⌊a / w⌋₊ ha hw' hfl, hW q χ a w ⌊a / w⌋₊ ha hw le_rfl]
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  have hpsi : Chebyshev.psi (a / w) = ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n := by
    unfold Chebyshev.psi; rfl
  rw [hpsi, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [← mul_sub, norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg]
  have h1 : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have h2 : ‖max (a / n - w') 0 - max (a / n - w) 0‖ ≤ w' - w := by
    have := abs_max_sub_max_le_abs (a / n - w') (a / n - w) 0
    rw [Real.norm_eq_abs]
    refine this.trans ?_
    rw [show a / n - w' - (a / n - w) = -(w' - w) by ring, abs_neg, abs_of_nonneg (by linarith)]
  calc Λ n * ‖χ (n : ZMod q)‖ * ‖max (a / n - w') 0 - max (a / n - w) 0‖
      ≤ Λ n * 1 * (w' - w) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 vonMangoldt_nonneg) h2 (norm_nonneg _)
        simp
    _ = Λ n * (w' - w) := by ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
