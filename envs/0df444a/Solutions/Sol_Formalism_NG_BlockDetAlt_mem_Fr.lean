-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.mem_Fr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:49.124976+00:00
-- url     : https://prove2.me/submissions/ae4e1f48-6db8-41a8-88f6-6a7bd240ecac

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution {T' : Subalgebra O (X' → O)} {φ : X' → FractionRing O} :
    φ ∈ Fr T' ↔ ∃ f ∈ T', ∀ x', algebraMap O (FractionRing O) (f x') = φ x' := by
  simp only [Fr, Subring.mem_map, Subalgebra.mem_toSubring]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, fun x' => rfl⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, funext h⟩
end Formalism.NG.BlockDetAlt
