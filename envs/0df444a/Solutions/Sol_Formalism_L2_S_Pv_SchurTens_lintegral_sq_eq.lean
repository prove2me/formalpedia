-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.lintegral_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:39.864808+00:00
-- url     : https://prove2.me/submissions/9ed96e74-012d-457f-bf75-889f78fffb8a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_enorm_sq_eq
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
private theorem aestronglyMeasurable_norm_sq {u : X → ℂ} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => ‖u x‖ ^ 2) μ := by
  exact hu.norm.pow 2
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
theorem _root_.solution {u : X → ℂ} (hu : MemLp u 2 μ) :
    ∫ x, ‖u x‖ ^ 2 ∂μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ).toReal := by
  have h0 : 0 ≤ᵐ[μ] fun x => ‖u x‖ ^ 2 := ae_of_all _ fun x => by
    exact sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae h0 (aestronglyMeasurable_norm_sq hu.1)]
  congr 1
  exact lintegral_congr fun x => (enorm_sq_eq (u x)).symm
end Formalism.L2.S.Pv.SchurTens
