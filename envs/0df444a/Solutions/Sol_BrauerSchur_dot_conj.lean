-- Prove2me | solution 1 for BrauerSchur.dot_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:16.42993+00:00
-- url     : https://prove2.me/submissions/071937e2-f16d-40a0-b6e8-b19c9a7e8b25

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
namespace BrauerSchur
theorem _root_.solution {h : G} (hh : h ∈ H) (y : G) : dot H ψ (h⁻¹ * y * h) = dot H ψ y := by
  classical
  unfold dot
  by_cases hy : y ∈ H
  · have hm : h⁻¹ * y * h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh
    rw [dif_pos hy, dif_pos hm]
    have e : (⟨h⁻¹ * y * h, hm⟩ : H) = (⟨h, hh⟩ : H)⁻¹ * ⟨y, hy⟩ * ⟨h, hh⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  · have hm : h⁻¹ * y * h ∉ H := fun hm => hy (by
      have e : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hh hm) (H.inv_mem hh))
    rw [dif_neg hy, dif_neg hm]
end BrauerSchur
