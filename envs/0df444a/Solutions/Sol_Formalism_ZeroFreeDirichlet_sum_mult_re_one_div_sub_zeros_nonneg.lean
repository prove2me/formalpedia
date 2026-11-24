-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.sum_mult_re_one_div_sub_zeros_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:13.233022+00:00
-- url     : https://prove2.me/submissions/9bba7a8b-53d6-4d65-aa28-a62d0cf101a0

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_NoZeroComplexOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_one_div_sub_zero_pos_ter

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
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + t * I - ρ)).re := by
  exact Finset.sum_nonneg fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_ter χ hχ ρ (hZ ρ hρ) σ t hσ).le
end Formalism.ZeroFreeDirichlet
