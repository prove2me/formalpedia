-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:37.98644+00:00
-- url     : https://prove2.me/submissions/e53474ae-19ac-49d7-870f-8e6ae44ce545

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at hh ⊢
  obtain ⟨hU, hfix, hz⟩ := hh
  have hd := isUnit_of_uh hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = (h⁻¹ * h) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = v := by rw [Matrix.nonsing_inv_mul h hd, Matrix.one_mulVec]
  exact ⟨uh_inv hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩
end Formalism.QuantumDeterminants.WeylGroupFacts
