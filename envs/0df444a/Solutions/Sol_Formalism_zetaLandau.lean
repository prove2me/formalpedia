-- Prove2me | solution 1 for Formalism.zetaLandau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:50:34.426083+00:00
-- url     : https://prove2.me/submissions/6eccaab0-0913-4637-b753-8b0b91361b9c

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_landau_Z
import Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_integrable_mellin
import Theorems.Thm_Formalism_Gz_bdd
import Theorems.Thm_Formalism_landauEq
import Theorems.Thm_Formalism_logDerivZeroFree
import Theorems.Thm_Formalism_mellinDeriv
import Theorems.Thm_Formalism_mellinElem
import Theorems.Thm_Formalism_mellinSgen
import Theorems.Thm_Formalism_riemannZetaOne_eq_mul_of_ne_one
import Theorems.Thm_Formalism_zetaRealNonvanish


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
open ArithmeticFunction
namespace Formalism
theorem _root_.solution : ZetaLandau := by
  intro s₀ hs₀ θ hθ0 hθ1 hCex s hs
  obtain ⟨C, x₀, hC⟩ := hCex
  obtain ⟨B, hB0, hB⟩ := Gz_bdd (le_max_right x₀ 1)
  have hs₀abs : |s₀| = 1 := by rcases hs₀ with h | h <;> simp [h]
  have hε : (-s₀) * (-s₀) = 1 := by rcases hs₀ with h | h <;> simp [h]
  have hCC : C ≤ max C B := le_max_left _ _
  have hBC : B ≤ max C B := le_max_right _ _
  have hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ (-s₀) (max C B) θ x := by
    intro x hx
    have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ0.le
    unfold HZ
    rcases le_or_gt x (max x₀ 1) with hxX | hxX
    · have h1 := hB x hx hxX
      have h2 : s₀ * Gz x ≤ B := by
        calc s₀ * Gz x ≤ |s₀ * Gz x| := le_abs_self _
          _ = |Gz x| := by rw [abs_mul, hs₀abs, one_mul]
          _ ≤ B := h1
      have h3 : B ≤ max C B * x ^ θ := by
        nlinarith [mul_nonneg (show 0 ≤ max C B by linarith) (show 0 ≤ x ^ θ - 1 by linarith)]
      linarith
    · have h1 := hC x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hxX))
      have h2 : C * x ^ θ ≤ max C B * x ^ θ := mul_le_mul_of_nonneg_right hCC (by linarith)
      linarith
  have hInt := landau_Z landauEq mellinSgen mellinElem zetaRealNonvanish
    hθ0 hθ1 hH
  have hZ1 := riemannZetaOne_ne_zero_of_integrable_mellin mellinDeriv mellinSgen mellinElem
    logDerivZeroFree hε hθ1 hH hInt s hs
  by_cases h1 : s = 1
  · subst h1
    exact riemannZeta_ne_zero_of_one_le_re (by simp)
  · rw [riemannZetaOne_eq_mul_of_ne_one h1] at hZ1
    exact right_ne_zero_of_mul hZ1
end Formalism
