-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exists_exceptional_zero_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:07.433699+00:00
-- url     : https://prove2.me/submissions/a0f27e7c-928f-4f41-9f52-548d7c79ae86

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zero_free_region_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (cZ c₁ : ℝ) (hle : c₁ ≤ cZ)
    (hZ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      InRegion cZ q s → IsLZero χ s →
        χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
        ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion cZ q s' → IsLZero χ' s' → χ' = χ ∧ s' = s)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : ∃ B : Finset ℝ, ExcZeros c₁ χ B := by
  by_cases h : ∃ s : ℂ, InRegion c₁ q s ∧ IsLZero χ s
  · obtain ⟨s, hs, hL⟩ := h
    obtain ⟨-, hχ1, him, hder, huniq⟩ := hZ q χ s (zero_free_region_mono hle hs) hL
    refine ⟨{s.re}, by simp, ?_, ?_⟩
    · intro β hβ
      rw [Finset.mem_singleton] at hβ
      subst hβ
      have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [← hs']
      exact ⟨hχ1, hs, hL.2, hder⟩
    · intro s' hs' hL'
      obtain ⟨-, hss⟩ := huniq χ s' (zero_free_region_mono hle hs') hL'
      refine ⟨s.re, Finset.mem_singleton_self _, ?_⟩
      rw [hss]
      exact Complex.ext (by simp) (by simp [him])
  · push_neg at h
    refine ⟨∅, by simp, by simp, ?_⟩
    intro s hs hL
    exact absurd hL (h s hs)
end Formalism.ZeroFreeDirichlet
