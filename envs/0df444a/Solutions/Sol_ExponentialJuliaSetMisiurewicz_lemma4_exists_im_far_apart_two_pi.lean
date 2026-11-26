-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma4_exists_im_far_apart_two_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:56.645176+00:00
-- url     : https://prove2.me/submissions/59db0bd3-836e-4487-a721-5516843f80b8

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_deriv_expIterate_add
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_two_pi_le_abs_im_sub_of_exp_eq
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_continuous_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiable_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma1_im_le_norm_deriv
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma3_ball_image_of_deriv_lower_bound
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite) :
    ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      2 * Real.pi ≤ |(expIterate n w).im - (expIterate n z).im| := by
  classical
  have hpi3 : (1 : ℝ) < Real.pi / 3 := by
    have := Real.pi_gt_three; linarith
  by_cases hall : ∀ n : ℕ, Set.InjOn (expIterate n) V
  · -- every iterate is injective on `V`
    set p : ℕ → Prop := fun n => Disjoint (expIterate n '' V) centralStrip with hp
    have hpinf : (Set.ofPred p).Infinite := hinf
    set r : ℕ → ℕ := fun n => Nat.nth p (n + 1) with hr
    have hrmem : ∀ n, Disjoint (expIterate (r n) '' V) centralStrip := fun n =>
      Nat.nth_mem_of_infinite hpinf (n + 1)
    have hrmono : ∀ n, r n < r (n + 1) := fun n =>
      (Nat.nth_lt_nth hpinf).mpr (by omega)
    have hrpos : ∀ n, 0 < r n := by
      intro n
      have h0 : Nat.nth p 0 < Nat.nth p (n + 1) := (Nat.nth_lt_nth hpinf).mpr (by omega)
      simp only [hr]
      omega
    have hout : ∀ n, ∀ z ∈ V, Real.pi / 3 < |(expIterate (r n) z).im| := by
      intro n z hz
      by_contra hc
      push Not at hc
      exact Set.disjoint_left.mp (hrmem n) ⟨z, hz, rfl⟩ hc
    -- geometric growth of the derivative along the chosen times
    have hgrow : ∀ n, ∀ z ∈ V, (Real.pi / 3) ^ n ≤ ‖deriv (expIterate (r n)) z‖ := by
      intro n
      induction n with
      | zero =>
          intro z hz
          have h1 := lemma1_im_le_norm_deriv (hrpos 0) z
          have h2 := hout 0 z hz
          simp only [pow_zero]
          linarith
      | succ n ih =>
          intro z hz
          have hlt := hrmono n
          have hk : 1 ≤ r (n + 1) - r n := by omega
          have hsplit : r (n + 1) = (r (n + 1) - r n) + r n := by omega
          have hchain : deriv (expIterate (r (n + 1))) z
              = deriv (expIterate (r (n + 1) - r n)) (expIterate (r n) z)
                * deriv (expIterate (r n)) z := by
            conv_lhs => rw [hsplit]
            exact deriv_expIterate_add _ _ z
          have hpt : expIterate (r (n + 1) - r n) (expIterate (r n) z)
              = expIterate (r (n + 1)) z := by
            conv_rhs => rw [hsplit]
            simp [expIterate, Function.iterate_add_apply]
          have h1 : Real.pi / 3
              ≤ ‖deriv (expIterate (r (n + 1) - r n)) (expIterate (r n) z)‖ := by
            have hl := lemma1_im_le_norm_deriv hk (expIterate (r n) z)
            rw [hpt] at hl
            have h2 := hout (n + 1) z hz
            linarith
          have h2 := ih z hz
          rw [hchain, norm_mul]
          have hnn : (0 : ℝ) ≤ (Real.pi / 3) ^ n := by positivity
          calc (Real.pi / 3) ^ (n + 1) = (Real.pi / 3) * (Real.pi / 3) ^ n := by ring
            _ ≤ ‖deriv (expIterate (r (n + 1) - r n)) (expIterate (r n) z)‖
                  * ‖deriv (expIterate (r n)) z‖ :=
                mul_le_mul h1 h2 hnn (norm_nonneg _)
    -- a ball inside `V`, blown up by Lemma 3
    obtain ⟨z0, hz0⟩ := hVne
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hVopen z0 hz0
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Real.pi / ρ) hpi3
    rw [div_lt_iff₀ hρ] at hn
    have hR : Real.pi < ρ * (Real.pi / 3) ^ n := by nlinarith
    have hinj3 : Set.InjOn (expIterate (r n)) (ball z0 ρ) := (hall (r n)).mono hball
    have himg := lemma3_ball_image_of_deriv_lower_bound hρ
      (by positivity : (0 : ℝ) ≤ (Real.pi / 3) ^ n)
      ((continuous_expIterate (r n)).continuousOn)
      ((differentiable_expIterate (r n)).differentiableOn)
      hinj3 (fun z hz => hgrow n z (hball hz))
    have hp1 : expIterate (r n) z0 + Complex.I * ((Real.pi : ℝ) : ℂ)
        ∈ ball (expIterate (r n) z0) (ρ * (Real.pi / 3) ^ n) := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      exact hR
    have hp2 : expIterate (r n) z0 - Complex.I * ((Real.pi : ℝ) : ℂ)
        ∈ ball (expIterate (r n) z0) (ρ * (Real.pi / 3) ^ n) := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      exact hR
    obtain ⟨w, hw, hwval⟩ := himg hp1
    obtain ⟨z, hz, hzval⟩ := himg hp2
    refine ⟨r n, w, z, hball hw, hball hz, ?_⟩
    rw [hwval, hzval]
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    rw [show (expIterate (r n) z0).im + Real.pi
        - ((expIterate (r n) z0).im - Real.pi) = 2 * Real.pi by ring]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  · -- some iterate fails to be injective on `V`
    push Not at hall
    have hex : ∃ n : ℕ, ¬ Set.InjOn (expIterate n) V := hall
    have hspec : ¬ Set.InjOn (expIterate (Nat.find hex)) V := Nat.find_spec hex
    have hzero : Nat.find hex ≠ 0 := by
      intro h0
      apply hspec
      rw [h0]
      intro a _ b _ hab
      simpa [expIterate] using hab
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hminj : Set.InjOn (expIterate m) V :=
      not_not.mp (Nat.find_min hex (by omega : m < Nat.find hex))
    rw [hm, Set.InjOn] at hspec
    push Not at hspec
    obtain ⟨w, hw, z, hz, heq, hne⟩ := hspec
    have hne' : expIterate m w ≠ expIterate m z := fun hc => hne (hminj hw hz hc)
    have hexp : Complex.exp (expIterate m w) = Complex.exp (expIterate m z) := by
      rw [← expIterate_succ, ← expIterate_succ]
      exact heq
    exact ⟨m, w, z, hw, hz, two_pi_le_abs_im_sub_of_exp_eq hexp hne'⟩
end ExponentialJuliaSetMisiurewicz
