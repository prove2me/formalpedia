-- Prove2me | solution 1 for CatSymplectic.Hemistrict.hemi_chain_map
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T22:25:33.995788+00:00
-- url     : https://prove2.me/submissions/3ccfb919-3033-4a08-b31a-34a1d38ef54c

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

open ContinuousAlternatingMap CatSymplectic.Hemistrict

namespace CSYhcmAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ham_spec (Ω : Form E 3) (F : Form E 1) (hF : F ∈ hamSubmodule Ω) :
    IsHamVF Ω F (hamVF Ω F) := by
  have h : ∃ v, IsHamVF Ω F v := hF.2
  unfold hamVF
  rw [dif_pos h]
  exact h.choose_spec

lemma hamVF_grad (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω) (f : E → ℝ) (hf : ContDiff ℝ smooth f) :
    hamVF Ω (ContWeatherall.grad f) = 0 := by
  have h0 : IsHamVF Ω (ContWeatherall.grad f) 0 := by
    refine ⟨contDiff_const, fun x => ?_⟩
    rw [ContWeatherall.extDeriv_grad hf]
    simp
  have uniq : ∀ u₁ u₂, IsHamVF Ω (ContWeatherall.grad f) u₁ →
      IsHamVF Ω (ContWeatherall.grad f) u₂ → u₁ = u₂ := by
    intro u₁ u₂ h1 h2
    funext x
    have e : (Ω x).curryLeft (u₁ x) = (Ω x).curryLeft (u₂ x) := by
      have := (h1.2 x).symm.trans (h2.2 x)
      exact neg_injective this
    have : (Ω x).curryLeft (u₁ x - u₂ x) = 0 := by
      rw [map_sub, e, sub_self]
    exact sub_eq_zero.mp (hΩ.2.2 x _ this)
  have h : ∃ u, IsHamVF Ω (ContWeatherall.grad f) u := ⟨0, h0⟩
  unfold hamVF
  rw [dif_pos h]
  exact uniq _ _ h.choose_spec h0

end CSYhcmAux

open CSYhcmAux

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F : hamSubmodule Ω) (f : smoothFns E) :
    ContWeatherall.grad (hemiFn Ω F f) =
      hemi Ω F (ContWeatherall.grad f) ∧
    hemi Ω (ContWeatherall.grad f) F = 0 := by
  have hf : ContDiff ℝ smooth (f : E → ℝ) := f.2
  have sF := ham_spec Ω F F.2
  set v := hamVF Ω F with hv
  have hvd : Differentiable ℝ v := sF.1.differentiable (by simp)
  have hf1 : ContDiff ℝ smooth (fderiv ℝ (f : E → ℝ)) :=
    hf.fderiv_right (m := smooth) (by simp)
  have hfd : Differentiable ℝ (fderiv ℝ (f : E → ℝ)) := hf1.differentiable (by simp)
  refine ⟨?_, ?_⟩
  · funext x
    ext w
    obtain ⟨a, rfl⟩ : ∃ a, w = ![a] := ⟨w 0, by funext i; fin_cases i; rfl⟩
    rw [ContWeatherall.grad_apply, ofSubsingleton_apply_apply]
    simp only [hemi, lieDeriv1, hemiFn, lieDerivFn, ← hv, ContinuousAlternatingMap.add_apply,
      compContinuousLinearMap_apply, Matrix.cons_val_zero]
    rw [show lieDerivFn v (f : E → ℝ) = fun y => fderiv ℝ (f : E → ℝ) y (v y) from rfl,
      fderiv_clm_apply (hfd x) (hvd x)]
    have hgd : DifferentiableAt ℝ (ContWeatherall.grad (f : E → ℝ)) x :=
      ((ContWeatherall.grad_contDiff hf).differentiable (by simp)) x
    rw [← fderiv_continuousAlternatingMap_apply_const_apply hgd]
    have eg : (fun y => ContWeatherall.grad (f : E → ℝ) y ![a]) = fun y => fderiv ℝ (f : E → ℝ) y a := by
      funext y; rw [ContWeatherall.grad_apply, ofSubsingleton_apply_apply]; rfl
    rw [eg, fderiv_clm_apply (hfd x) (differentiableAt_const a)]
    have h2 : minSmoothness ℝ 2 ≤ smooth := by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top
    have hsym := (hf.contDiffAt (x := x)).isSymmSndFDerivAt h2
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.flip_apply, fderiv_const, fderiv_fun_const,
      Pi.zero_apply, zero_apply, _root_.map_zero, zero_add, add_zero]
    rw [ContWeatherall.grad_apply, ofSubsingleton_apply_apply, hsym]
    simp only [Function.comp_apply, Matrix.cons_val_zero, fderiv_fun_const, Pi.zero_apply,
      zero_apply, _root_.map_zero, add_zero]
    ring
  · rw [hemi, hamVF_grad Ω hΩ f hf]
    funext x
    ext w
    simp [lieDeriv1]
