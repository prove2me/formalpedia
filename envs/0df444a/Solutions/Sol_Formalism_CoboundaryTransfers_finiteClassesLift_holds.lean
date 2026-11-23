-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.finiteClassesLift_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:22.70905+00:00
-- url     : https://prove2.me/submissions/8bde5ab7-94dc-481b-8723-916a57c64e86

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_LenBound
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.CoboundaryTransfers
section SlopeTestRemainingChoices
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
private theorem WachMod.mem_cocycles_units_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := by
  simp [WachMod.Z1, WachMod.d1, sub_eq_add_neg]
end SlopeTestRemainingChoices
end Formalism.CoboundaryTransfers
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : LiftHf := by
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g eW c
    hnat hcl₁ hint hlifts κ hκ
  obtain ⟨pr, hcoc, hpr⟩ := hint.2 κ hκ
  obtain ⟨y₁, z₁, hcoc₁, hy, hz⟩ := hlifts _ _ hcoc
  have hmem : ((y₁, z₁) : D₁ × D₁) ∈ W₁.Z1 := (WachMod.mem_cocycles_units_iff W₁ _).mpr hcoc₁.2
  refine ⟨cl₁ ⟨(y₁, z₁), hmem⟩, hcl₁ _ hcoc₁, ?_⟩
  have hpr' : ((c • pr : W₂.Z1) : D₂ × D₂) = S.π.f2 (⟨(y₁, z₁), hmem⟩ : W₁.Z1) := by
    show c • (pr : D₂ × D₂) = (S.π.f y₁, S.π.f z₁)
    rw [hy, hz]
    rfl
  rw [hnat _ _ hpr', map_smul, hpr, smul_smul, mul_comm]
end Formalism.CoboundaryTransfers
