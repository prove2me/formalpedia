-- Prove2me | solution 1 for CatSymplectic.Hemistrict.unique_hamVF
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:44:16.788285+00:00
-- url     : https://prove2.me/submissions/64678f35-e308-4e91-86cf-fc6ae47bd618

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

open CatSymplectic.Hemistrict

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F : Form E 1) (v w : E → E)
    (hv : IsHamVF Ω F v) (hw : IsHamVF Ω F w) :
    v = w ∧ hamVF Ω F = v := by
  have uniq : ∀ v w : E → E, IsHamVF Ω F v → IsHamVF Ω F w → v = w := by
    intro v w hv hw
    funext x
    have h1 := hv.2 x
    have h2 := hw.2 x
    rw [h1, neg_inj] at h2
    have : (Ω x).curryLeft (v x - w x) = 0 := by rw [map_sub, h2, sub_self]
    exact sub_eq_zero.mp (hΩ.2.2 x _ this)
  refine ⟨uniq v w hv hw, ?_⟩
  have hex : ∃ u, IsHamVF Ω F u := ⟨v, hv⟩
  unfold hamVF
  rw [dif_pos hex]
  exact uniq _ _ hex.choose_spec hv
