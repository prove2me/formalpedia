-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.image_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:25.81286+00:00
-- url     : https://prove2.me/submissions/35cbb814-5cb7-40b7-a620-1af204d8bd79

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_image_eq_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution [Fintype σ] (Φ t Φ₂ t₂ : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, constantCoeff (Φ x) = 0) (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (heq : ∀ x, subst t (Φ x) = X x)
    (hΦ0₂ : ∀ x, constantCoeff (Φ₂ x) = 0) (hΦ₂ : ∀ x, IntS v (Φ₂ x))
    (hL₂ : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ₂ x)).det = 0)
    (ht0₂ : ∀ y, constantCoeff (t₂ y) = 0) (heq₂ : ∀ x, subst t₂ (Φ₂ x) = X x) :
    {F : MvPowerSeries σ C | ∃ γ, IntS v γ ∧ F = subst t γ} =
      {F : MvPowerSeries σ C | ∃ γ, IntS v γ ∧ F = subst t₂ γ} := by
  rw [image_eq_int Φ t hΦ0 hΦ hL ht0 heq, image_eq_int Φ₂ t₂ hΦ0₂ hΦ₂ hL₂ ht0₂ heq₂]
end Formalism.L2.FormalSeriesBounds.AltInv
