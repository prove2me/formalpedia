-- Prove2me | solution 1 for CompanionTheory.Rg.FlB.inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:29:41.776203+00:00
-- url     : https://prove2.me/submissions/32691219-94f0-41f1-bdf1-3bd948d2ab1d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.Rg CompanionTheory.Rg.FlB
namespace CompanionTheory.Rg.FlB
theorem _root_.solution (L : Type) [NontriviallyNormedField L] (n : ℕ) [IsUltrametricDist L] :
    ∃ Λ : AddSubgroup (Fin n → L), IsLat L Λ ∧ IsCong Λ (0 : L) (1 : (Fin n → L) ≃ₗ[L] (Fin n → L)) := by
  refine ⟨⟨⟨⟨{x | ∀ i, ‖x i‖ ≤ 1}, fun {a b} ha hb i => ?_⟩, fun i => by simp⟩, fun {a} ha i => by simpa using ha i⟩,
    ⟨n, Pi.basisFun L (Fin n), fun x => by simp⟩, fun x hx => ⟨x, hx, by simp⟩⟩
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
end CompanionTheory.Rg.FlB
