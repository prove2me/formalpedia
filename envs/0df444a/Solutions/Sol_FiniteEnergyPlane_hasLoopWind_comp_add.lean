-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T10:12:44.051794+00:00
-- url     : https://prove2.me/submissions/6eb06f7d-1ff9-4ea4-adda-11f9bc8ebb0b

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_exists_int_forall_mem_Ioo_of_forall_ne
import Mathlib.Analysis.Calculus.Deriv.Shift



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A winding number is unchanged by shifting the parameter of the loop. -/
theorem h310_hasLoopWind_shift {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) (d : ℝ) :
    HasLoopWind (fun t => f (t + d)) k := by
  obtain ⟨hfc, hper, hf0, θ, hθc, hθ, hθk⟩ := hf
  have hpi := Real.pi_pos
  -- `θ(t + 1) - θ(t)` lies in `2πℤ`
  have hint : ∀ t, ∃ n : ℤ, θ (t + 1) - θ t = 2 * π * n := by
    intro t
    have hn : (‖f t‖ : ℂ) ≠ 0 := by simpa using hf0 t
    have he : Complex.exp ((θ (t + 1) : ℂ) * Complex.I) = Complex.exp ((θ t : ℂ) * Complex.I) := by
      have h1 := hθ (t + 1)
      rw [hper t] at h1
      exact mul_left_cancel₀ hn (h1.symm.trans (hθ t))
    have he1 : Complex.exp (((θ (t + 1) - θ t : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he1
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  have havoid : ∀ t, ∀ m : ℤ, θ (t + 1) - θ t ≠ π + m * (2 * π) := by
    intro t m h
    obtain ⟨n, hn⟩ := hint t
    rw [hn] at h
    have h2 : (2 : ℝ) * (n - m) = 2 * m - 2 * m + 1 := by nlinarith
    have h3 : (2 : ℝ) * (n - m) = 1 := by linarith
    have h4 : (2 : ℤ) * (n - m) = 1 := by exact_mod_cast h3
    omega
  obtain ⟨m, hm⟩ := exists_int_forall_mem_Ioo_of_forall_ne (fun t => θ (t + 1) - θ t)
    ((hθc.comp (continuous_id.add continuous_const)).sub hθc) π (2 * π) (by positivity) havoid
  have hsmall : ∀ t, |θ (t + 1) - θ t - (θ 1 - θ 0)| < 2 * π := by
    intro t
    have h0 := hm 0
    have ht := hm t
    simp only [zero_add] at h0
    rw [abs_lt]
    constructor <;> nlinarith [h0.1, h0.2, ht.1, ht.2]
  have hconst : ∀ t, θ (t + 1) - θ t = θ 1 - θ 0 := by
    intro t
    obtain ⟨n, hn⟩ := hint t
    have h0 : θ 1 - θ 0 = 2 * π * k := hθk
    have hs := hsmall t
    rw [hn, h0, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hs
    have h1 : |((n : ℝ) - k)| < 1 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have h2 : |n - k| < 1 := by exact_mod_cast h1
    have : n = k := by rw [abs_lt] at h2; omega
    rw [hn, h0, this]
  refine ⟨hfc.comp (continuous_id.add continuous_const), fun t => ?_, fun t => hf0 _,
    fun t => θ (t + d), hθc.comp (continuous_id.add continuous_const), fun t => hθ (t + d), ?_⟩
  · show f (t + 1 + d) = f (t + d)
    rw [add_right_comm]; exact hper _
  · show θ (1 + d) - θ (0 + d) = 2 * π * k
    rw [zero_add, add_comm 1 d, hconst d]; exact hθk

theorem h310_isAsymptoticEigen_shift {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1)
    (P P' : ReebOrbit H) (c : ℝ) (hT : P'.T = P.T) (hx : ∀ τ, P'.x τ = P.x (τ + c))
    {μ : ℝ} {v : ℝ → V 1} (hv : IsAsymptoticEigen J P μ v) :
    IsAsymptoticEigen J P' μ (fun t => v (t + c / P.T)) := by
  have hTpos := P.T_pos
  have hxT : ∀ t, P'.x (P'.T * t) = P.x (P.T * (t + c / P.T)) := by
    intro t
    rw [hx, hT]
    congr 1
    field_simp
  obtain ⟨⟨hvs, hvp, hvxi⟩, ⟨t₀, ht₀⟩, hveq⟩ := hv
  refine ⟨⟨hvs.comp (contDiff_id.add contDiff_const), fun t => ?_, fun t => ?_⟩,
    ⟨t₀ - c / P.T, by simpa using ht₀⟩, fun t => ?_⟩
  · show v (t + 1 + c / P.T) = v (t + c / P.T)
    rw [add_right_comm]; exact hvp _
  · rw [hxT]; exact hvxi _
  · have hd : deriv (fun t => v (t + c / P.T)) t = deriv v (t + c / P.T) :=
      deriv_comp_add_const _ _ _
    unfold asympOp
    rw [hd, hxT, hT]
    exact hveq (t + c / P.T)

theorem h310_hasEigenWind_shift {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1)
    (P P' : ReebOrbit H) (c : ℝ) (hT : P'.T = P.T) (hx : ∀ τ, P'.x τ = P.x (τ + c))
    {μ : ℝ} {k : ℤ} (h : HasEigenWind J P μ k) : HasEigenWind J P' μ k := by
  have hTpos := P.T_pos
  have hx' : ∀ τ, P.x τ = P'.x (τ + -c) := by
    intro τ; rw [hx]; congr 1; ring
  obtain ⟨⟨v, hv⟩, hall⟩ := h
  refine ⟨⟨_, h310_isAsymptoticEigen_shift J P P' c hT hx hv⟩, fun w hw => ?_⟩
  have hw' := h310_isAsymptoticEigen_shift J P' P (-c) hT.symm hx' hw
  have hwind := h310_hasLoopWind_shift (hall _ hw') (c / P.T)
  have hxT : ∀ t, P'.x (P'.T * t) = P.x (P.T * (t + c / P.T)) := by
    intro t
    rw [hx, hT]
    congr 1
    field_simp
  unfold HasXiLoopWind
  convert hwind using 2 with t
  rw [hxT, hT]
  congr 2
  ring

theorem hasEigenWind_iff_of_shift_aux {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1)
    (P P' : ReebOrbit H) (c : ℝ) (hT : P'.T = P.T) (hx : ∀ τ, P'.x τ = P.x (τ + c))
    (μ : ℝ) (k : ℤ) :
    HasEigenWind J P μ k ↔ HasEigenWind J P' μ k := by
  have hx' : ∀ τ, P.x τ = P'.x (τ + -c) := by
    intro τ; rw [hx]; congr 1; ring
  exact ⟨h310_hasEigenWind_shift J P P' c hT hx, h310_hasEigenWind_shift J P' P (-c) hT.symm hx'⟩

end FiniteEnergyPlane

namespace FiniteEnergyPlane

theorem hasLoopWind_comp_add_aux {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) (d : ℝ) :
    HasLoopWind (fun t => f (t + d)) k :=
  h310_hasLoopWind_shift hf d

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) (d : ℝ) :
    HasLoopWind (fun t => f (t + d)) k :=
  FiniteEnergyPlane.hasLoopWind_comp_add_aux hf d
