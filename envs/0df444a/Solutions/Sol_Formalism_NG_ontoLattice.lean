-- Prove2me | solution 1 for Formalism.NG.ontoLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:42.01984+00:00
-- url     : https://prove2.me/submissions/dd4279b2-5d6c-42c8-895f-9d36a1afb96c

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IdemNormalForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatOntoLattice := by
  intro O A L _ _ _ _ _ _ _ _ φ hφ
  have hle : (⊤ : Submodule O (Module.End O L)) ≤
      LinearMap.range φ.toLinearMap ⊔ IsLocalRing.maximalIdeal O • ⊤ := by
    intro f _
    obtain ⟨a, ha⟩ := hφ f
    have hf : f = φ a + (f - φ a) := by abel
    rw [hf]
    exact Submodule.add_mem_sup (LinearMap.mem_range.mpr ⟨a, rfl⟩) ha
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  intro f
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (htop Submodule.mem_top)
  exact ⟨a, ha⟩
end Formalism.NG
