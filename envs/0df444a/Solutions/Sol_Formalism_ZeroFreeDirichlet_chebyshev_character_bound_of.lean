-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_character_bound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:04:59.751049+00:00
-- url     : https://prove2.me/submissions/68dfc94c-75e3-4d0d-a3b0-9f53ad6025d0

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PsiChiBoundOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_nonprincipal_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_principal_character_bound

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
theorem _root_.solution : PsiChiBoundOf := by
  intro hS hG c₁ hc₁ hc₁'
  obtain ⟨cs, Cs, hcs, hSm⟩ := hS c₁ hc₁ hc₁'
  obtain ⟨cg, Kg, hcg, hGz⟩ := hG
  set c₀ := min (min cs cg) 1 with hc0def
  have hc0 : 0 < c₀ := lt_min (lt_min hcs hcg) one_pos
  have hc01 : c₀ ≤ 1 := min_le_right _ _
  have hc0s : c₀ ≤ cs := (min_le_left _ _).trans (min_le_left _ _)
  have hc0g : c₀ ≤ cg := (min_le_left _ _).trans (min_le_right _ _)
  set Cs' := max Cs 0
  set Kg' := max Kg 0
  refine ⟨c₀ / 4, 128 / c₀ ^ 2 + 2 + 4 * Cs' + 4 * Kg' + 16, by positivity, ?_⟩
  intro q _ χ B x hB hx hq
  have he4 : 0 ≤ x * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log x)) := by positivity
  have hCs' : 0 ≤ Cs' := le_max_right _ _
  have hKg' : 0 ≤ Kg' := le_max_right _ _
  by_cases hχ : χ = 1
  · have hB0 : B = ∅ := Finset.eq_empty_of_forall_notMem fun β hβ => (hB.2.1 β hβ).1 hχ
    subst hχ hB0
    rw [if_pos rfl, Finset.sum_empty, add_zero]
    have hG' : ∀ z : ℝ, x ≤ z → |Formalism.Gz z| ≤ Kg' * z * Real.exp (-cg * Real.sqrt (Real.log z)) := by
      intro z hz
      refine (hGz z (by linarith)).trans ?_
      have : 0 ≤ z * Real.exp (-cg * Real.sqrt (Real.log z)) := by
        have : 0 ≤ z := by linarith
        positivity
      nlinarith [le_max_left Kg 0]
    have := chebyshev_principal_character_bound (q := q) hc0 hc01 hc0g hKg' hx hq hG'
    nlinarith
  · rw [if_neg hχ, sub_zero]
    have hE : ∀ z : ℝ, x ≤ z →
        ‖Schi χ z - negLD χ 1 * z + ∑ β ∈ B, (z : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
          Cs' * z * Real.exp (-cs * Real.sqrt (Real.log z)) := by
      intro z hz
      have hqz : (q : ℝ) ≤ Real.exp (cs * Real.sqrt (Real.log z)) := by
        refine hq.trans (Real.exp_le_exp.2 ?_)
        have h1 : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log z) :=
          Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hz)
        have h0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
        have h0' : 0 ≤ Real.sqrt (Real.log z) := Real.sqrt_nonneg _
        nlinarith
      refine (hSm q χ B z hχ hB (by linarith) hqz).trans ?_
      have : 0 ≤ z * Real.exp (-cs * Real.sqrt (Real.log z)) := by
        have : 0 ≤ z := by linarith
        positivity
      nlinarith [le_max_left Cs 0]
    have := chebyshev_character_nonprincipal_bound χ hχ hc₁ hc₁' B hB hc0 hc01 hc0s hCs' hx hE
    nlinarith
end Formalism.ZeroFreeDirichlet
