-- Prove2me | solution 1 for ContactCalculus.extDeriv_naturality_of_tangent_pullback_on_regular_level
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:39:30.449978+00:00
-- url     : https://prove2.me/submissions/193d5bbe-b5d6-4322-86cc-dc7607610b61

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_ImplicitCalculus_smooth_level_parametrization

set_option autoImplicit false
open GrayStability Filter
open scoped ContDiff Topology

theorem solution {n c m : ℕ} (F : E n → E c) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ z ∈ levelSet F, Function.Surjective (fderiv ℝ F z))
    (α : OneForm m) (β : OneForm n)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (f : E n → E m) (hf : ContDiff ℝ ∞ f)
    (hpull : ∀ z ∈ levelSet F, ∀ v ∈ tangentSpace F z,
      α (f z) (fderiv ℝ f z v) = β z v)
    (y : E n) (hy : y ∈ levelSet F) (u v : E n)
    (hu : u ∈ tangentSpace F y) (hv : v ∈ tangentSpace F y) :
    extDerivOneForm α (f y) (fderiv ℝ f y u) (fderiv ℝ f y v) =
      extDerivOneForm β y u v := by
  let D := fderiv ℝ F y
  let uk : D.ker := ⟨u, hu⟩
  let vk : D.ker := ⟨v, hv⟩
  obtain ⟨γ, hγ, hγ0, hγD, hlevel⟩ :=
    ImplicitCalculus.smooth_level_parametrization F y hF.contDiffAt (hreg y hy)
  have hγd := hγD.differentiableAt
  have hγ1 : ContDiffAt ℝ 1 γ 0 := hγ.of_le (by decide)
  have hγev : ∀ᶠ z in 𝓝 (0 : D.ker), DifferentiableAt ℝ γ z := by
    filter_upwards [hγ1.eventually (by simp)] with z hz
    exact hz.differentiableAt (by simp)
  have hzero : ∀ᶠ z in 𝓝 (0 : D.ker), fderiv ℝ (fun a => F (γ a)) z = 0 := by
    have heq : (fun a => F (γ a)) =ᶠ[𝓝 (0 : D.ker)] (fun _ => F y) := hlevel
    filter_upwards [heq.fderiv (𝕜 := ℝ)] with z hz
    change fderiv ℝ (fun a => F (γ a)) z = fderiv ℝ (fun _ : D.ker => F y) z at hz
    simpa only [fderiv_const_apply] using hz
  let P : D.ker → (D.ker →L[ℝ] ℝ) :=
    fun z => (α (f (γ z))).comp (fderiv ℝ (fun a => f (γ a)) z)
  let Q : D.ker → (D.ker →L[ℝ] ℝ) :=
    fun z => (β (γ z)).comp (fderiv ℝ γ z)
  have heq : P =ᶠ[𝓝 (0 : D.ker)] Q := by
    filter_upwards [hlevel, hzero, hγev] with z hz hz0 hzd
    have hzM : γ z ∈ levelSet F := hz.trans hy
    have htan : ∀ a : D.ker, fderiv ℝ γ z a ∈ tangentSpace F (γ z) := by
      intro a
      have hc := fderiv_comp z (hF.differentiable (by simp) (γ z)) hzd
      simp only [Function.comp_def] at hc
      have he := congrArg (fun L : D.ker →L[ℝ] E c => L a) hc
      rw [hz0] at he
      exact he.symm
    ext a
    dsimp [P, Q]
    have hc := fderiv_comp z (hf.differentiable (by simp) (γ z)) hzd
    simp only [Function.comp_def] at hc
    rw [hc]
    exact hpull (γ z) hzM (fderiv ℝ γ z a) (htan a)
  have hpair : fderiv ℝ P 0 uk vk - fderiv ℝ P 0 vk uk =
      fderiv ℝ Q 0 uk vk - fderiv ℝ Q 0 vk uk := by
    rw [heq.fderiv_eq]
  have hfg : ContDiffAt ℝ ∞ (fun a => f (γ a)) 0 :=
    hf.contDiffAt.comp 0 hγ
  have hP := ContactCalculus.exterior_pairing_pullback α (fun a => f (γ a)) 0 uk vk
    (hα.differentiable (by simp) (f (γ 0))) (hfg.of_le (by decide))
  have hQ := ContactCalculus.exterior_pairing_pullback β γ 0 uk vk
    (hβ.differentiable (by simp) (γ 0)) (hγ.of_le (by decide))
  have hcomp : fderiv ℝ (fun a => f (γ a)) 0 =
      (fderiv ℝ f y).comp D.ker.subtypeL := by
    have hc := fderiv_comp 0 (hf.differentiable (by simp) (γ 0)) hγd
    simpa only [Function.comp_def, hγ0, hγD.fderiv] using hc
  dsimp only [P, Q] at hpair
  rw [hP, hQ] at hpair
  simpa only [hγ0, hcomp, hγD.fderiv, ContinuousLinearMap.comp_apply,
    Submodule.coe_subtypeL, Submodule.coe_subtype, Subtype.coe_mk, uk, vk, extDerivOneForm] using hpair
