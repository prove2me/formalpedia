-- Prove2me | solution 1 for Formalism.Pfun_ne_zero_of_one_le_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:05.676839+00:00
-- url     : https://prove2.me/submissions/c628995a-8c0b-4c4f-8d95-41dd317fba18

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Theorems.Thm_Formalism_Pfun_eq_of_ne
import Theorems.Thm_Formalism_Pfun_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
namespace Formalism
theorem _root_.solution (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : Pfun χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1
    rw [Pfun_one]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  · rw [Pfun_eq_of_ne χ h1]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs))
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs)
end Formalism
