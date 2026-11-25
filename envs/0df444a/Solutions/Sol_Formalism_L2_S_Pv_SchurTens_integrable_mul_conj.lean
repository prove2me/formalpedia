-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.integrable_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:43.674854+00:00
-- url     : https://prove2.me/submissions/9c486d07-33cf-47d5-90db-a470c554f7dc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
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
theorem _root_.solution {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * conj (v x)) μ := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  have hm : AEStronglyMeasurable (fun x => u x * conj (v x)) μ :=
    hu.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hv.1)
  refine (hu2.add hv2).mono hm (ae_of_all _ fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ ‖‖u x‖ ^ 2 + ‖v x‖ ^ 2‖
  rw [norm_mul, norm_conj_complex, Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x),
    mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x))]
end Formalism.L2.S.Pv.SchurTens
