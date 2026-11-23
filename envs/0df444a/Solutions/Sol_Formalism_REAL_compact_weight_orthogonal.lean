-- Prove2me | solution 1 for Formalism.REAL.compact_weight_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:52.66458+00:00
-- url     : https://prove2.me/submissions/258771d5-432d-43e6-b6b9-e6a4f489a1ae

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight

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
theorem _root_.solution : KWtOrth := by
  intro V _ _ n ε F μ ν x y hU hx hy hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
    by_contra h; push Not at h; exact hne (funext h)
  have h1 := hU a a rfl x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
  have h2 : ((μ a : ℂ) - (ν a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by
    rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (by exact_mod_cast sub_eq_zero.mp h) ha
  · exact h
end Formalism.REAL
