-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BesselUnitaryEquiv.integral_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:45.833066+00:00
-- url     : https://prove2.me/submissions/f6f3e85b-9f57-4ec3-a2b9-5d68a7ec4301

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BesselUnitaryEquiv
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.BesselUnitaryEquiv
theorem _root_.solution {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    (f : α → α) (hf : MeasurePreserving f μ μ) (hfe : MeasurableEmbedding f)
    (L : E ≃L[ℂ] F) (I₀ : α → E) (I₁ : α → F)
    (h : ∀ᵐ p ∂μ, I₁ (f p) = L (I₀ p)) : ∫ p, I₁ p ∂μ = L (∫ p, I₀ p ∂μ) := by
  rw [← hf.integral_comp hfe I₁, integral_congr_ae h]
  exact L.integral_comp_comm I₀
end Formalism.QuantumDeterminants.BesselUnitaryEquiv
