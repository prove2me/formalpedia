-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.re_one_div_sub_zero_pos_ter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:23.462904+00:00
-- url     : https://prove2.me/submissions/615d2eaf-8cc3-4d97-ab9a-47e54732635c

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_NoZeroComplexOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + t * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ
  have hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
  have hwpos : 0 < ((σ : ℂ) + t * I - ρ).re := by rw [hwre]; linarith
  have hw0 : (σ : ℂ) + t * I - ρ ≠ 0 := fun h => by rw [h] at hwpos; simp at hwpos
  rw [one_div, Complex.inv_re]
  exact div_pos hwpos (Complex.normSq_pos.mpr hw0)
end Formalism.ZeroFreeDirichlet
