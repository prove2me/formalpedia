-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.memLp_two_of_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:36:44.549783+00:00
-- url     : https://prove2.me/submissions/d892dfc0-f6f6-4f92-94f4-649ffd061e39

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
theorem _root_.solution {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (h : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ < ⊤) :
    MemLp u 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hu).2 ⟨aestronglyMeasurable_norm_sq hu, ?_⟩
  have e : ∀ x, ‖‖u x‖ ^ 2‖ₑ = ‖u x‖ₑ ^ 2 := fun x => by
    rw [Real.enorm_of_nonneg (by positivity), enorm_sq_eq]
  rw [hasFiniteIntegral_iff_enorm]
  simp only [e]
  exact h
end Formalism.L2.S.Pv.SchurTens
