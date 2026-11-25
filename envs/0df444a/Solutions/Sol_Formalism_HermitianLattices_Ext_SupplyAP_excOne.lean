-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.excOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:58.80961+00:00
-- url     : https://prove2.me/submissions/13088ca0-6dd1-4ec1-a6fa-6237b100fa5e

import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcOne
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exists_exceptional_zero_set
import Theorems.Thm_Formalism_ZeroFreeDirichlet_half_le_of_real_in_region
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zFRDirichlet
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zero_free_region_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 20 ∧
    ∀ (m : ℕ) [NeZero m], ∃ B : DirichletCharacter ℂ m → Finset ℝ,
      (∀ χ, ExcZeros c₁ χ (B χ)) ∧
      (∀ χ χ', (B χ).Nonempty → (B χ').Nonempty → χ = χ') ∧
      (∀ χ, ∀ β ∈ B χ, χ ^ 2 = 1 ∧ χ ≠ 1 ∧ 1 / 2 ≤ β ∧
        DirichletCharacter.LFunction χ (β : ℂ) = 0) := by
  obtain ⟨cZ, hcZ, hZ⟩ := zFRDirichlet
  refine ⟨min cZ (1 / 20), lt_min hcZ (by norm_num), min_le_right _ _, fun m _ => ?_⟩
  have hex := fun χ : DirichletCharacter ℂ m =>
    exists_exceptional_zero_set cZ (min cZ (1 / 20)) (min_le_left _ _) hZ m χ
  refine ⟨fun χ => Classical.choose (hex χ), fun χ => Classical.choose_spec (hex χ), ?_, ?_⟩
  · rintro χ χ' ⟨β, hβ⟩ ⟨β', hβ'⟩
    obtain ⟨h1, hreg, hz, _⟩ := (Classical.choose_spec (hex χ)).2.1 β hβ
    obtain ⟨h1', hreg', hz', _⟩ := (Classical.choose_spec (hex χ')).2.1 β' hβ'
    have := (hZ m χ β (zero_free_region_mono (min_le_left _ _) hreg) ⟨Or.inl h1, hz⟩).2.2.2.2 χ' β'
      (zero_free_region_mono (min_le_left _ _) hreg') ⟨Or.inl h1', hz'⟩
    exact this.1.symm
  · intro χ β hβ
    obtain ⟨h1, hreg, hz, _⟩ := (Classical.choose_spec (hex χ)).2.1 β hβ
    have hZ1 := hZ m χ β (zero_free_region_mono (min_le_left _ _) hreg) ⟨Or.inl h1, hz⟩
    exact ⟨hZ1.1, h1, half_le_of_real_in_region (min_le_right _ _) hreg, hz⟩
end Formalism.HermitianLattices.Ext.SupplyAP
