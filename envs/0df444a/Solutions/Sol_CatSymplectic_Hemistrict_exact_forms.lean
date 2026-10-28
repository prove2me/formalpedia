-- Prove2me | solution 1 for CatSymplectic.Hemistrict.exact_forms
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:45:07.219427+00:00
-- url     : https://prove2.me/submissions/3df21a83-afd0-41f3-a62b-8c6a214f9198

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

open CatSymplectic.Hemistrict

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (f : E → ℝ) (hf : ContDiff ℝ smooth f) :
    ContWeatherall.grad f ∈ hamSubmodule Ω ∧
      hamVF Ω (ContWeatherall.grad f) = 0 := by
  have h0 : IsHamVF Ω (ContWeatherall.grad f) 0 := by
    refine ⟨contDiff_const, fun x => ?_⟩
    rw [ContWeatherall.extDeriv_grad hf]
    simp
  have uniq : ∀ v w : E → E, IsHamVF Ω (ContWeatherall.grad f) v →
      IsHamVF Ω (ContWeatherall.grad f) w → v = w := by
    intro v w hv hw
    funext x
    have h1 := hv.2 x
    have h2 := hw.2 x
    rw [h1, neg_inj] at h2
    have : (Ω x).curryLeft (v x - w x) = 0 := by rw [map_sub, h2, sub_self]
    exact sub_eq_zero.mp (hΩ.2.2 x _ this)
  refine ⟨⟨ContWeatherall.grad_contDiff hf, 0, h0⟩, ?_⟩
  have hex : ∃ u, IsHamVF Ω (ContWeatherall.grad f) u := ⟨0, h0⟩
  unfold hamVF
  rw [dif_pos hex]
  exact uniq _ _ hex.choose_spec h0
