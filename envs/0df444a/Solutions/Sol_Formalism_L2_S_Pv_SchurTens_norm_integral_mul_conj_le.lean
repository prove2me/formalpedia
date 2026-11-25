-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.norm_integral_mul_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:21:37.908553+00:00
-- url     : https://prove2.me/submissions/686b85e9-ee8c-4595-9e5d-27f25ab336f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_integrable_mul_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
namespace Formalism.L2.S.Pv.SchurTens
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
private theorem norm_conj_complex (z : ℂ) : ‖conj z‖ = ‖z‖ := Complex.norm_conj z
private theorem mul_le_weighted_sq_add_half {a b t : ℝ} (ht : 0 < t) : a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
  have h : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have ht1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have e : (t * a - b) ^ 2 / t = t * a ^ 2 - 2 * (a * b) + b ^ 2 / t := by
    linear_combination (t * a ^ 2 - 2 * a * b) * ht1
  linarith
end Formalism.L2.S.Pv.SchurTens
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) {t : ℝ} (ht : 0 < t) :
    ‖∫ x, u x * conj (v x) ∂μ‖ ≤ (t * ∫ x, ‖u x‖ ^ 2 ∂μ + (∫ x, ‖v x‖ ^ 2 ∂μ) / t) / 2 := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  have hR : Integrable (fun x => (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2) μ :=
    ((hu2.const_mul t).add (hv2.div_const t)).div_const 2
  have h1 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2 ∂μ
      = (∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ) / 2 := integral_div _ _
  have h2 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ
      = ∫ x, t * ‖u x‖ ^ 2 ∂μ + ∫ x, ‖v x‖ ^ 2 / t ∂μ :=
    integral_add (hu2.const_mul t) (hv2.div_const t)
  have h3 : ∫ x, t * ‖u x‖ ^ 2 ∂μ = t * ∫ x, ‖u x‖ ^ 2 ∂μ := integral_const_mul _ _
  have h4 : ∫ x, ‖v x‖ ^ 2 / t ∂μ = (∫ x, ‖v x‖ ^ 2 ∂μ) / t := integral_div _ _
  rw [← h4, ← h3, ← h2, ← h1]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono (integrable_mul_conj hu hv).norm hR fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2
  rw [norm_mul, norm_conj_complex]
  exact mul_le_weighted_sq_add_half ht
end Formalism.L2.S.Pv.SchurTens
