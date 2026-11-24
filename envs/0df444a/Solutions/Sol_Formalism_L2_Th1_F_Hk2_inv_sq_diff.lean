-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.inv_sq_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:34:02.914035+00:00
-- url     : https://prove2.me/submissions/4ecf0500-f8a1-4fa6-87b6-e7262500981e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2
namespace Formalism.L2.Th1.F.Hk2
theorem _root_.solution {ρ : ℝ} {w w' : ℂ} (hρ : 0 < ρ) (hw : ρ ≤ ‖w‖) (hw' : ρ ≤ ‖w'‖) :
    ‖(w ^ 2)⁻¹ - (w' ^ 2)⁻¹‖ ≤ 2 * (ρ ^ 3)⁻¹ * ‖w - w'‖ := by
  have h0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hρ hw)
  have h0' : w' ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hρ hw')
  have e : (w ^ 2)⁻¹ - (w' ^ 2)⁻¹ = (w' - w) * (w⁻¹ * (w' ^ 2)⁻¹ + (w ^ 2)⁻¹ * w'⁻¹) := by
    field_simp
    ring
  have i1 : ‖w‖⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ hw
  have i2 : ‖w'‖⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ hw'
  have p1 : 0 ≤ ‖w‖⁻¹ := by positivity
  have p2 : 0 ≤ ‖w'‖⁻¹ := by positivity
  have b1 : ‖w⁻¹ * (w' ^ 2)⁻¹‖ ≤ (ρ ^ 3)⁻¹ := by
    rw [norm_mul, norm_inv, norm_inv, norm_pow, ← inv_pow, ← inv_pow]
    calc ‖w‖⁻¹ * ‖w'‖⁻¹ ^ 2 ≤ ρ⁻¹ * ρ⁻¹ ^ 2 := by gcongr
      _ = ρ⁻¹ ^ 3 := by ring
  have b2 : ‖(w ^ 2)⁻¹ * w'⁻¹‖ ≤ (ρ ^ 3)⁻¹ := by
    rw [norm_mul, norm_inv, norm_inv, norm_pow, ← inv_pow, ← inv_pow]
    calc ‖w‖⁻¹ ^ 2 * ‖w'‖⁻¹ ≤ ρ⁻¹ ^ 2 * ρ⁻¹ := by gcongr
      _ = ρ⁻¹ ^ 3 := by ring
  rw [e, norm_mul, norm_sub_rev w' w, mul_comm]
  gcongr
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (ρ ^ 3)⁻¹ + (ρ ^ 3)⁻¹ := add_le_add b1 b2
    _ = 2 * (ρ ^ 3)⁻¹ := by ring
end Formalism.L2.Th1.F.Hk2
