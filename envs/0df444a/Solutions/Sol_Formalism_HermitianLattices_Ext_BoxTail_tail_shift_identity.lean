-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_shift_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:25:16.019252+00:00
-- url     : https://prove2.me/submissions/97492caf-cdfb-49d8-b2f7-4d8847a8e5c0

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RectShiftChi
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourA
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_shift_alg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_formula_character
import Theorems.Thm_Formalism_ZeroFreeDirichlet_rectangle_contour_shift_character


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (y σ₁ T : ℝ)
    (hy : 1 ≤ y) (hσ₁ : 0 < σ₁) (hσ₁' : σ₁ < 1) (hT : 0 < T)
    (hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T → DirichletCharacter.LFunction χ w ≠ 0) :
    (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y - Formalism.ZeroFreeDirichlet.negLD χ 1 * y) =
      (∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      + I * ((∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - ∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (T : ℂ) * I))
      + ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y ((σ₁ : ℂ) + (u : ℂ) * I) := by
  obtain ⟨hint, hS⟩ := Formalism.ZeroFreeDirichlet.perron_formula_character N χ y hy 2 (by norm_num)
  have hrect := Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character N χ hχ y (by linarith) σ₁ 2 T ∅ hσ₁ hσ₁' (by norm_num) hT
    (by simp) (fun w h1 h2 h3 hL => absurd hL (hzf w h1 h2 h3)) (by simp)
  simp only [Finset.sum_empty, sub_zero] at hrect
  unfold Formalism.ZF.rectInt at hrect
  rw [← integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint,
    ← intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith)] at hS
  exact tail_shift_alg _ _ _ _ _ _ _ hS hrect
end Formalism.HermitianLattices.Ext.BoxTail
