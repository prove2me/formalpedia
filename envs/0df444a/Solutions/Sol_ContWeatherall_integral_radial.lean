-- Prove2me | solution 1 for ContWeatherall.integral_radial
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-18T21:49:56.92227+00:00
-- url     : https://prove2.me/submissions/4c95382f-205d-49e3-b15b-37bf50cbffbd

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

theorem ir_main {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (n : ℕ) {g : E → G} (hg : ContDiff ℝ 1 g) (x : E) :
    ∫ t in (0 : ℝ)..1, (((n + 1 : ℕ) : ℝ) * t ^ n) • g (t • x) + t ^ (n + 1) • fderiv ℝ g (t • x) x
      = g x := by
  have hd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ (n + 1) • g (t • x))
      ((((n + 1 : ℕ) : ℝ) * t ^ n) • g (t • x) + t ^ (n + 1) • fderiv ℝ g (t • x) x) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 : HasDerivAt (fun t : ℝ => g (t • x)) (fderiv ℝ g (t • x) x) t :=
      (hd (t • x)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 := (hasDerivAt_pow (n + 1) t).smul h2
    convert h3 using 1
    · rfl
    · rw [Nat.add_sub_cancel, add_comm]
  have hcont : Continuous fun t : ℝ =>
      (((n + 1 : ℕ) : ℝ) * t ^ n) • g (t • x) + t ^ (n + 1) • fderiv ℝ g (t • x) x := by
    have : Continuous fun t : ℝ => fderiv ℝ g (t • x) := hc.comp (continuous_id.smul continuous_const)
    have : Continuous fun t : ℝ => fderiv ℝ g (t • x) x := this.clm_apply continuous_const
    have : Continuous fun t : ℝ => g (t • x) := hd.continuous.comp (continuous_id.smul continuous_const)
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable _ _)]
  simp

end ContWeatherall

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (n : ℕ) {g : E → G} (hg : ContDiff ℝ 1 g) (x : E) :
    ∫ t in (0 : ℝ)..1, (((n + 1 : ℕ) : ℝ) * t ^ n) • g (t • x) + t ^ (n + 1) • fderiv ℝ g (t • x) x
      = g x :=
  ContWeatherall.ir_main n hg x
