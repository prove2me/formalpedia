-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.local_density_product
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:23.193322+00:00
-- url     : https://prove2.me/submissions/70939afe-5931-4f15-81f6-7a6ec9223916

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : ValuationProductBound := by
  intro B _ s vh ve vt q A r hq hs hvh hve hvt hA1 hA2
  have hq0 : 0 < q := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  constructor
  · rw [← Real.rpow_mul hq0.le, ← Real.rpow_sum_of_pos hq0]
    apply Real.rpow_le_rpow_of_exponent_le hq
    calc ∑ b, 2 * (s b : ℝ) * vh b ≤ ∑ b, 2 * ((r : ℝ) + 1) * vh b := by
          refine Finset.sum_le_sum fun b _ => ?_
          have : (s b : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast (hs b).2
          have := hvh b
          gcongr
      _ = 2 * ((r : ℝ) + 1) * ∑ b, vh b := by rw [Finset.mul_sum]
      _ ≤ 2 * ((r : ℝ) + 1) * A := by gcongr
      _ = _ := by ring
  · rw [← Real.rpow_mul hq0.le, ← Real.rpow_sum_of_pos hq0]
    apply Real.rpow_le_rpow_of_exponent_le hq
    calc ∑ b, vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2) ≤ ∑ b, ((r : ℝ) + 1) / 2 * ve b := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h1 : (s b : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast (hs b).2
          have h2 : (1 : ℝ) ≤ (s b : ℝ) := by exact_mod_cast (hs b).1
          have h3 : vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2) = (ve b - vh b) * (((s b : ℝ) - 1) / 2) := by
            rw [← hvt b]; ring
          rw [h3]
          have := hvh b
          have := hve b
          nlinarith [mul_nonneg (hvh b) (sub_nonneg.2 h2), mul_nonneg (hve b) (sub_nonneg.2 h1)]
      _ = ((r : ℝ) + 1) / 2 * ∑ b, ve b := by rw [Finset.mul_sum]
      _ ≤ ((r : ℝ) + 1) / 2 * A := by gcongr
      _ = _ := by ring
end Formalism.HermitianLatticeCounting.P.S4aux
