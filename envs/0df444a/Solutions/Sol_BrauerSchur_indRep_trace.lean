-- Prove2me | solution 1 for BrauerSchur.indRep_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:16.624802+00:00
-- url     : https://prove2.me/submissions/45156555-6b07-47cb-b0fc-fd4008c16d4a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_InducedCharRealised
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_Induced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open BrauerSchur
open scoped BigOperators
variable {G : Type*} [Group G] {K : Type*} [Field K] (H : Subgroup G) (ψ : H →* Kˣ)
variable {m : ℕ} (t : Fin m → G)
namespace BrauerSchur
theorem _root_.solution (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H)
    (g : G) : LinearMap.trace K (Fin m → K) (indRep H ψ t ht hc g) = ∑ i, dot H ψ ((t i)⁻¹ * g * t i) := by
  show LinearMap.trace K (Fin m → K) (Matrix.toLin' (indMat H ψ t g)) = _
  rw [Matrix.trace_toLin'_eq]
  rfl
end BrauerSchur
