-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.assemblyNG2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:23.620926+00:00
-- url     : https://prove2.me/submissions/efe5b4af-8d62-4614-862d-1ea1b8986097

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution (H1 : TypeCS) : AssemblyNG2 := by
  intro c
  refine ⟨4 * c, ?_⟩
  intro k e H nn D Ty _ _ w amp μ be I hH hnn hw hcard hbe hI hIbe hμ hμI hsum hamp
  set A : ℝ := H ^ (c * e) with hA
  have hA0 : 0 ≤ A := by positivity
  have step : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ A * A * nn := by
    intro t
    have hb : 0 < be t ^ (k - 1) := by have := hbe t; positivity
    calc ∑ d, w d * ‖amp t d‖ ^ 2 ≤ ∑ d, (A * I t ^ (k - 1)) * (w d * μ t d) := by
          refine Finset.sum_le_sum fun d _ => ?_
          have h1 : ‖amp t d‖ ^ 2 ≤ (A * I t ^ (k - 1)) * μ t d := by
            calc ‖amp t d‖ ^ 2 ≤ μ t d ^ 2 := by
                  exact pow_le_pow_left₀ (norm_nonneg _) (hamp t d) 2
              _ = μ t d * μ t d := by ring
              _ ≤ (A * I t ^ (k - 1)) * μ t d := mul_le_mul_of_nonneg_right (hμI t d) (hμ t d)
          calc w d * ‖amp t d‖ ^ 2 ≤ w d * ((A * I t ^ (k - 1)) * μ t d) :=
                mul_le_mul_of_nonneg_left h1 (hw d)
            _ = _ := by ring
      _ = (A * I t ^ (k - 1)) * ∑ d, w d * μ t d := by rw [Finset.mul_sum]
      _ ≤ (A * I t ^ (k - 1)) * (A * (be t ^ (k - 1))⁻¹ * nn) :=
          mul_le_mul_of_nonneg_left (hsum t) (mul_nonneg hA0 (pow_nonneg (hI t) _))
      _ = A * A * nn * (I t ^ (k - 1) * (be t ^ (k - 1))⁻¹) := by ring
      _ ≤ A * A * nn * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← div_eq_mul_inv, div_le_one hb]
          exact pow_le_pow_left₀ (hI t) (hIbe t) _
      _ = A * A * nn := by ring
  calc ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ (Fintype.card Ty : ℝ) * ∑ t, ∑ d, w d * ‖amp t d‖ ^ 2 :=
        H1 D Ty w amp hw
    _ ≤ (Fintype.card Ty : ℝ) * ∑ _t : Ty, A * A * nn :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => step t) (Nat.cast_nonneg _)
    _ = (Fintype.card Ty : ℝ) * (Fintype.card Ty : ℝ) * (A * A * nn) := by simp; ring
    _ ≤ A * A * (A * A * nn) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hcard hcard (Nat.cast_nonneg _) hA0
    _ = H ^ (4 * c * e) * nn := by
        rw [hA, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; ring
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
