-- Prove2me | solution 1 for Formalism.REAL.kIrr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:15.444233+00:00
-- url     : https://prove2.me/submissions/f14b42f3-b936-4113-8f6e-d0ed32658c9f

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Theorems.Thm_Formalism_REAL_compactSpan_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (he : KHiExist) (hu : KHiUniq) : KIrr := by
  intro V _ _ n ε F μ x hfd hrel hunit hx S hS hSst
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  haveI := hfd
  have hfdS : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hS
  obtain ⟨y, hyS, hy0, ν, hy⟩ := he V n ε F S hfdS hrel hunit hSst h0
  rcases hu V n ε F μ ν x y hrel hunit hx (hS hyS) hy with h | ⟨-, c, hc⟩
  · exact absurd h hy0
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hy0 hc
    have hxS : x ∈ S := by
      have h1 : c⁻¹ • y ∈ S := S.smul_mem _ hyS
      rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h1
    exact le_antisymm hS (compactSpan_le hxS hSst)
end Formalism.REAL
