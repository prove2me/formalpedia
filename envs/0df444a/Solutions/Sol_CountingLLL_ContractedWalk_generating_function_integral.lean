-- Prove2me | solution 1 for CountingLLL.ContractedWalk.generating_function_integral
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:14:27.79037+00:00
-- url     : https://prove2.me/submissions/778fdd98-d587-40a9-a131-7d7d21878f47

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_recursion
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_bounds

set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped Interval

noncomputable section

private theorem cubic_unique (θ z g h : ℝ) (ht0 : 0 ≤ θ) (ht : θ < 1/3)
    (hz0 : 0 ≤ z) (hz : z ≤ 1) (hg0 : 0 ≤ g) (hg : g ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hgEq : g = 1-θ+θ*z*g^3) (hhEq : h = 1-θ+θ*z*h^3) : g = h := by
  have hg2 : g^2 ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg)]
  have hh2 : h^2 ≤ 1 := by nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh)]
  have hgh : g*h ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hh)]
  have hs0 : 0 ≤ g^2+g*h+h^2 := by positivity
  have hs : g^2+g*h+h^2 ≤ 3 := by nlinarith
  have htz0 : 0 ≤ θ*z := mul_nonneg ht0 hz0
  have htz : θ*z ≤ θ := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hz)]
  have hterm : θ*z*(g^2+g*h+h^2) ≤ 3*θ := by
    nlinarith [mul_nonneg htz0 (sub_nonneg.mpr hs), mul_nonneg (sub_nonneg.mpr htz) (by norm_num : (0:ℝ) ≤ 3)]
  have hpos : 0 < 1-θ*z*(g^2+g*h+h^2) := by nlinarith
  have hd : (g-h)*(1-θ*z*(g^2+g*h+h^2)) = 0 := by nlinarith [hgEq,hhEq]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right (ne_of_gt hpos))

private theorem cubic_lipschitz (θ x y g h : ℝ) (ht0 : 0 ≤ θ) (ht : θ < 1/3)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 ≤ y) (hy : y ≤ 1)
    (hg0 : 0 ≤ g) (hg : g ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hgEq : g = 1-θ+θ*x*g^3) (hhEq : h = 1-θ+θ*y*h^3) :
    |g-h| ≤ θ/(1-3*θ)*|x-y| := by
  have hg2 : g^2 ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg)]
  have hh2 : h^2 ≤ 1 := by nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh)]
  have hgh : g*h ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hh)]
  have hs0 : 0 ≤ g^2+g*h+h^2 := by positivity
  have hs : g^2+g*h+h^2 ≤ 3 := by nlinarith
  have hp : |g^3-h^3| ≤ 3*|g-h| := by
    rw [show g^3-h^3 = (g-h)*(g^2+g*h+h^2) by ring, abs_mul, abs_of_nonneg hs0]
    nlinarith [mul_nonneg (abs_nonneg (g-h)) (sub_nonneg.mpr hs)]
  have hg3 : 0 ≤ g^3 := pow_nonneg hg0 _
  have hg3le : g^3 ≤ 1 := pow_le_one₀ hg0 hg
  have hpiece : |x*g^3-y*h^3| ≤ |x-y| + 3*|g-h| := by
    have heq : x*g^3-y*h^3 = (x-y)*g^3+y*(g^3-h^3) := by ring
    rw [heq]
    calc
      _ ≤ |(x-y)*g^3|+|y*(g^3-h^3)| := abs_add_le _ _
      _ = |x-y| * g^3 + y * |g^3-h^3| := by rw [abs_mul, abs_mul, abs_of_nonneg hg3, abs_of_nonneg hy0]
      _ ≤ |x-y|+3*|g-h| := by
        nlinarith [mul_nonneg (abs_nonneg (x-y)) (sub_nonneg.mpr hg3le),
          mul_nonneg (sub_nonneg.mpr hy) (abs_nonneg (g^3-h^3)), mul_nonneg hy0 (sub_nonneg.mpr hp)]
  have hdiff : g-h = θ*(x*g^3-y*h^3) := by nlinarith [hgEq,hhEq]
  have hdabs : |g-h| = θ*|x*g^3-y*h^3| := by rw [hdiff, abs_mul, abs_of_nonneg ht0]
  have hineq : |g-h| ≤ θ*(|x-y| + 3*|g-h|) := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hpiece)]
  have hden : 0 < 1-3*θ := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem gf_continuous (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) :
    ContinuousOn (generatingFunction θ) (Set.Icc (0:ℝ) 1) := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  let C := θ/(1-3*θ)
  have hden : 0 < 1-3*θ := by linarith
  have hC : 0 ≤ C := div_nonneg hθ0 (le_of_lt hden)
  let δ := ε/(C+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  refine ⟨δ,hδ,?_⟩
  intro y hy hdist
  have hθ1 : θ ≤ 1 := by linarith
  have hGx := generating_function_bounds θ x hθ1 hx.1 hx.2
  have hGy := generating_function_bounds θ y hθ1 hy.1 hy.2
  have hxEq := generating_function_recursion θ x hθ0 hθ hx.1 hx.2
  have hyEq := generating_function_recursion θ y hθ0 hθ hy.1 hy.2
  have hlip := cubic_lipschitz θ y x (generatingFunction θ y) (generatingFunction θ x)
    hθ0 hθ hy.1 hy.2 hx.1 hx.2 hGy.1 hGy.2 hGx.1 hGx.2 hyEq hxEq
  change |generatingFunction θ y - generatingFunction θ x| ≤ C*|y-x| at hlip
  rw [Real.dist_eq] at hdist ⊢
  have hδid : (C+1)*δ = ε := by dsimp [δ]; field_simp
  have hgap : 0 < δ-|y-x| := by linarith
  nlinarith [mul_nonneg hC (le_of_lt hgap), abs_nonneg (y-x)]

private def invGF (θ x : ℝ) : ℝ := (x-(1-θ))/(θ*x^3)
private def invGF' (θ x : ℝ) : ℝ := (3*(1-θ)-2*x)/(θ*x^4)

private theorem inv_range (θ x : ℝ) (ht0 : 0 < θ) (ht : θ < 1/3)
    (hx : x ∈ Set.Icc (1-θ) 1) : invGF θ x ∈ Set.Icc (0:ℝ) 1 := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hden : 0 < θ*x^3 := by positivity
  have hx2 : x^2 ≤ 1 := by nlinarith [mul_nonneg (le_of_lt hxpos) (sub_nonneg.mpr hx.2)]
  have hsum0 : 0 ≤ 1+x+x^2 := by positivity
  have hsum : 1+x+x^2 ≤ 3 := by linarith [hx.2]
  have hcoeff : 0 ≤ 1-θ*(1+x+x^2) := by
    have := mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr hsum)
    nlinarith
  have hpoly : 0 ≤ (1-x)*(1-θ*(1+x+x^2)) := mul_nonneg (sub_nonneg.mpr hx.2) hcoeff
  constructor
  · exact div_nonneg (by linarith [hx.1]) (le_of_lt hden)
  · apply (div_le_one hden).2
    nlinarith

private theorem inv_root (θ x : ℝ) (ht0 : 0 < θ) (ht : θ < 1/3)
    (hx : x ∈ Set.Icc (1-θ) 1) : x = 1-θ+θ*(invGF θ x)*x^3 := by
  have hxpos : 0 < x := by linarith [hx.1]
  dsimp [invGF]
  field_simp
  <;> ring

private theorem inv_right (θ x : ℝ) (ht0 : 0 < θ) (ht : θ < 1/3)
    (hx : x ∈ Set.Icc (1-θ) 1) : generatingFunction θ (invGF θ x) = x := by
  have hrange := inv_range θ x ht0 ht hx
  have hg := generating_function_bounds θ (invGF θ x) (by linarith) hrange.1 hrange.2
  have heq := generating_function_recursion θ (invGF θ x) (le_of_lt ht0) ht hrange.1 hrange.2
  exact cubic_unique θ (invGF θ x) (generatingFunction θ (invGF θ x)) x (le_of_lt ht0) ht
    hrange.1 hrange.2 hg.1 hg.2 (by linarith [hx.1]) hx.2 heq (inv_root θ x ht0 ht hx)

private theorem inv_deriv (θ x : ℝ) (ht0 : 0 < θ) (ht : θ < 1/3)
    (hx : x ∈ Set.Icc (1-θ) 1) : HasDerivAt (invGF θ) (invGF' θ x) x := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hden : θ*x^3 ≠ 0 := by positivity
  have hcalc := ((hasDerivAt_id x).sub_const (1-θ)).div
    ((hasDerivAt_const x θ).mul ((hasDerivAt_id x).pow 3)) hden
  convert hcalc using 1 <;> try rfl
  dsimp [invGF']
  field_simp
  <;> ring

private theorem inv_deriv_cont (θ : ℝ) (ht0 : 0 < θ) (ht : θ < 1/3) :
    ContinuousOn (invGF' θ) (Set.Icc (1-θ) 1) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    positivity

private def anti (θ x : ℝ) : ℝ := ((-(3*(1-θ))/2)/x^2 + 2/x)/θ

private theorem anti_deriv (θ x : ℝ) (ht0 : 0 < θ) (ht : θ < 1/3)
    (hx : x ∈ Set.Icc (1-θ) 1) : HasDerivAt (anti θ) (x*invGF' θ x) x := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hcalc := (((hasDerivAt_const x (-(3*(1-θ))/2)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero _ hx0)).add
      ((hasDerivAt_const x (2:ℝ)).div (hasDerivAt_id x) hx0)).div_const θ
  convert hcalc using 1 <;> try rfl
  dsimp [invGF']
  field_simp
  <;> ring

theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) :
    (∫ z in (0:ℝ)..1, generatingFunction θ z) = 1-θ/(2*(1-θ)) := by
  by_cases hz : θ = 0
  · have hpoint : Set.EqOn (generatingFunction θ) (fun _ : ℝ => 1) [[(0:ℝ),1]] := by
      intro z hz'
      have hz'' : z ∈ Set.Icc (0:ℝ) 1 := by simpa using hz'
      have hh := generating_function_recursion θ z hθ0 hθ hz''.1 hz''.2
      simp [hz] at hh
      simpa [hz] using hh
    rw [intervalIntegral.integral_congr hpoint]
    simp [hz]
  · have ht0 : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hz)
    have ha : 1-θ ≤ 1 := by linarith
    have hInv0 : invGF θ (1-θ) = 0 := by simp [invGF]
    have hInv1 : invGF θ 1 = 1 := by
      dsimp [invGF]
      field_simp
      <;> ring
    have hd : ∀ x ∈ [[1-θ,1]], HasDerivAt (invGF θ) (invGF' θ x) x := by
      intro x hx
      exact inv_deriv θ x ht0 hθ (by simpa [Set.uIcc_of_le ha] using hx)
    have hc : ContinuousOn (invGF' θ) [[1-θ,1]] := by
      simpa [Set.uIcc_of_le ha] using inv_deriv_cont θ ht0 hθ
    have hg : ContinuousOn (generatingFunction θ) (invGF θ '' [[1-θ,1]]) := by
      apply (gf_continuous θ hθ0 hθ).mono
      rintro y ⟨x,hx,rfl⟩
      exact inv_range θ x ht0 hθ (by simpa [Set.uIcc_of_le ha] using hx)
    have hchange := intervalIntegral.integral_comp_mul_deriv' hd hc hg
    rw [hInv0,hInv1] at hchange
    have hcongr : (∫ x in (1-θ)..1, (generatingFunction θ ∘ invGF θ) x * invGF' θ x) =
        ∫ x in (1-θ)..1, x * invGF' θ x := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [Function.comp_apply]
      rw [inv_right θ x ht0 hθ (by simpa [Set.uIcc_of_le ha] using hx)]
    rw [hcongr] at hchange
    have hD : ∀ x ∈ [[1-θ,1]], HasDerivAt (anti θ) (x*invGF' θ x) x := by
      intro x hx
      exact anti_deriv θ x ht0 hθ (by simpa [Set.uIcc_of_le ha] using hx)
    have hcont : ContinuousOn (fun x => x * invGF' θ x) [[1-θ,1]] := continuousOn_id.mul hc
    have hanti := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hcont.intervalIntegrable
    rw [hanti] at hchange
    have hvalue : anti θ 1 - anti θ (1-θ) = 1-θ/(2*(1-θ)) := by
      have ha0 : 1-θ ≠ 0 := by linarith
      have ht0' : θ ≠ 0 := ne_of_gt ht0
      dsimp [anti]
      field_simp
      <;> ring
    rw [hvalue] at hchange
    exact hchange.symm
