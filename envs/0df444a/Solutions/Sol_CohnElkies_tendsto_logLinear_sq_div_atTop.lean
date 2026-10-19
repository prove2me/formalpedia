-- Prove2me | solution 1 for CohnElkies.tendsto_logLinear_sq_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/8abfed60-e3a6-4417-8b5f-9a9bbcab484f

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto
      (fun ℓ : ℝ => (20 * Real.log ℓ + 1) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  have hlog1 : Tendsto
      (fun ℓ : ℝ => Real.log ℓ / ℓ)
      atTop (𝓝 0) := by
    simpa using!
      Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
  have hlog2 : Tendsto
      (fun ℓ : ℝ => Real.log ℓ ^ 2 / ℓ)
      atTop (𝓝 0) := by
    simpa using!
      Real.tendsto_pow_log_div_mul_add_atTop
        1 0 2 (by norm_num : (1 : ℝ) ≠ 0)
  have hinv : Tendsto
      (fun ℓ : ℝ => (1 : ℝ) / ℓ)
      atTop (𝓝 0) := by
    simpa [one_div] using!
      (tendsto_inv_atTop_zero :
        Tendsto (fun ℓ : ℝ => ℓ⁻¹)
          atTop (𝓝 0))
  convert! ((hlog2.const_mul 400).add
    (hlog1.const_mul 40)).add hinv using 1
  · funext ℓ
    ring
  · norm_num
end CohnElkies
