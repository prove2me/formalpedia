-- Prove2me | solution 1 for CubicTurning.energy_eq_halfAngleEnergy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:38:51.031402+00:00
-- url     : https://prove2.me/submissions/8507fa31-0d0a-4e1b-acf5-9f55097786c6

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning









































theorem half_angle_pair_identity (x₀ y₀ r₀ x₁ y₁ r₁ : ℝ)
    (h₀ : r₀^2=x₀^2+y₀^2) (h₁ : r₁^2=x₁^2+y₁^2)
    (hw₀ : r₀+x₀ ≠ 0) (hw₁ : r₁+x₁ ≠ 0) :
    (r₀+x₀)*(r₁+x₁)*(y₀/(r₀+x₀)-y₁/(r₁+x₁))^2 =
      2*(r₀*r₁-x₀*x₁-y₀*y₁) := by
  field_simp
  linear_combination -(r₁+x₁)^2*h₀-(r₀+x₀)^2*h₁













theorem pairEnergy_unit_mul (u : ℂ) (hu : ‖u‖=1) (d₀ d₁ : ℂ) :
    pairEnergy (u*d₀) (u*d₁)=pairEnergy d₀ d₁ := by
  have huc : u*conj u=1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hu]
    norm_num
  unfold pairEnergy
  rw [norm_mul,norm_mul,hu,one_mul,one_mul]
  have he : u*d₀*conj (u*d₁)=(u*conj u)*(d₀*conj d₁) := by
    simp only [map_mul]
    ring
  rw [he,huc,one_mul]






















































end CubicTurning

open CubicTurning in
theorem solution (e d₀ d₁ : ℂ) (hf : IsForward e d₀ d₁) :
    energy e d₀ d₁=halfAngleEnergy e d₀ d₁ := by
  rcases hf with ⟨he,h₀,h₁⟩
  unfold energy halfAngleEnergy
  split_ifs with hc
  · have hd₀ : d₀≠0 := by intro hz; subst d₀; norm_num [halfSlope] at hc
    have hd₁ : d₁≠0 := by intro hz; subst d₁; norm_num [halfSlope] at hc
    have hw₀ : ‖d₀‖+(e*d₀).re≠0 := ne_of_gt (by linarith [norm_pos_iff.mpr hd₀])
    have hw₁ : ‖d₁‖+(e*d₁).re≠0 := ne_of_gt (by linarith [norm_pos_iff.mpr hd₁])
    have hs₀ : ‖d₀‖^2=(e*d₀).re^2+(e*d₀).im^2 := by
      have hh := Complex.normSq_eq_norm_sq (z:=e*d₀)
      rw [Complex.normSq_apply,norm_mul,he,one_mul] at hh
      simpa only [pow_two] using hh.symm
    have hs₁ : ‖d₁‖^2=(e*d₁).re^2+(e*d₁).im^2 := by
      have hh := Complex.normSq_eq_norm_sq (z:=e*d₁)
      rw [Complex.normSq_apply,norm_mul,he,one_mul] at hh
      simpa only [pow_two] using hh.symm
    have hid := half_angle_pair_identity (e*d₀).re (e*d₀).im ‖d₀‖
      (e*d₁).re (e*d₁).im ‖d₁‖ hs₀ hs₁ hw₀ hw₁
    rw [←pairEnergy_unit_mul e he]
    unfold pairEnergy
    have hprod : ((e*d₀)*conj (e*d₁)).re =
        (e*d₀).re*(e*d₁).re+(e*d₀).im*(e*d₁).im := by
      simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,mul_neg,sub_neg_eq_add]
    rw [hprod]
    simp only [norm_mul,he,one_mul]
    dsimp only [halfSlope]
    linarith [hid]
  · rfl
