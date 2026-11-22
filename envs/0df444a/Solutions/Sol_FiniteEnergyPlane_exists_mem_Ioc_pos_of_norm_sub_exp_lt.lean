-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mem_Ioc_pos_of_norm_sub_exp_lt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T13:02:22.444186+00:00
-- url     : https://prove2.me/submissions/b7dead3b-21a5-4ede-9915-e3896a8821a1

import Mathlib



/-!
# (D) A path close to `e^{iψ}` with `ψ` increasing by `3π` crosses the positive real axis
-/

namespace FiniteEnergyPlane

open Set
open scoped Real

theorem exists_mem_Ioc_pos_of_norm_sub_exp_lt_aux (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℂ) (ψ : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc a b)) (hψ : ContinuousOn ψ (Set.Icc a b))
    (hclose : ∀ σ ∈ Set.Icc a b, ‖g σ - Complex.exp ((ψ σ : ℂ) * Complex.I)‖ < 1)
    (hinc : ψ a + 3 * π ≤ ψ b) :
    ∃ σ ∈ Set.Ioc a b, 0 < (g σ).re ∧ (g σ).im = 0 := by
  set h : ℝ → ℂ := fun σ => g σ * Complex.exp (((-ψ σ : ℝ) : ℂ) * Complex.I) with hh
  have hexp : ∀ σ, Complex.exp ((ψ σ : ℂ) * Complex.I) *
      Complex.exp (((-ψ σ : ℝ) : ℂ) * Complex.I) = 1 := by
    intro σ; rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
  have hnexp : ∀ x : ℝ, ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
    fun x => Complex.norm_exp_ofReal_mul_I x
  have hh1 : ∀ σ ∈ Icc a b, ‖h σ - 1‖ < 1 := by
    intro σ hσ
    have e : h σ - 1 = (g σ - Complex.exp ((ψ σ : ℂ) * Complex.I)) *
        Complex.exp (((-ψ σ : ℝ) : ℂ) * Complex.I) := by
      simp only [hh]; rw [sub_mul, hexp]
    rw [e, norm_mul, hnexp, mul_one]; exact hclose σ hσ
  have hre : ∀ σ ∈ Icc a b, 0 < (h σ).re := by
    intro σ hσ
    have h1 := hh1 σ hσ
    have h2 : |(h σ - 1).re| ≤ ‖h σ - 1‖ := Complex.abs_re_le_norm _
    have h3 : (h σ - 1).re = (h σ).re - 1 := by simp
    rw [h3] at h2
    have := neg_abs_le ((h σ).re - 1)
    linarith
  have hslit : ∀ σ ∈ Icc a b, h σ ∈ Complex.slitPlane := fun σ hσ => Or.inl (hre σ hσ)
  have hhc : ContinuousOn h (Icc a b) := by
    have : ContinuousOn (fun σ => (((-ψ σ : ℝ) : ℂ) * Complex.I)) (Icc a b) :=
      (Complex.continuous_ofReal.comp_continuousOn hψ.neg).mul continuousOn_const
    exact hg.mul this.cexp
  set Θ : ℝ → ℝ := fun σ => ψ σ + Complex.arg (h σ) with hΘ
  have hΘc : ContinuousOn Θ (Icc a b) := by
    refine hψ.add ?_
    intro σ hσ
    exact (Complex.continuousAt_arg (hslit σ hσ)).comp_continuousWithinAt (hhc σ hσ)
  have harg : ∀ σ ∈ Icc a b, |Complex.arg (h σ)| < π / 2 := by
    intro σ hσ
    exact Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre σ hσ))
  have hgΘ : ∀ σ ∈ Icc a b, g σ = (‖g σ‖ : ℂ) * Complex.exp ((Θ σ : ℂ) * Complex.I) := by
    intro σ hσ
    have hgh : g σ = h σ * Complex.exp ((ψ σ : ℂ) * Complex.I) := by
      simp only [hh]; rw [mul_assoc, mul_comm (Complex.exp _) (Complex.exp _), hexp, mul_one]
    have hn : ‖g σ‖ = ‖h σ‖ := by rw [hgh, norm_mul, hnexp, mul_one]
    rw [hn]
    conv_lhs => rw [hgh, ← Complex.norm_mul_exp_arg_mul_I (h σ)]
    simp only [hΘ]; push_cast
    rw [mul_assoc, ← Complex.exp_add]; ring_nf
  have ha := harg a ⟨le_rfl, hab⟩
  have hb := harg b ⟨hab, le_rfl⟩
  have hΘab : Θ a + 2 * π < Θ b := by
    simp only [hΘ]
    have := abs_lt.1 ha; have := abs_lt.1 hb
    linarith
  -- the target multiple of `2π`
  set k : ℤ := ⌊Θ a / (2 * π)⌋ + 1 with hk
  have hpi : 0 < 2 * π := by positivity
  have hk1 : Θ a < 2 * π * k := by
    have := Int.lt_floor_add_one (Θ a / (2 * π))
    rw [div_lt_iff₀ hpi] at this
    simp only [hk]; push_cast; linarith
  have hk2 : 2 * π * k ≤ Θ a + 2 * π := by
    have := Int.floor_le (Θ a / (2 * π))
    rw [le_div_iff₀ hpi] at this
    simp only [hk]; push_cast; linarith
  obtain ⟨σ, hσ, hσΘ⟩ := intermediate_value_Icc hab hΘc ⟨hk1.le, by linarith⟩
  have hσa : σ ≠ a := by rintro rfl; linarith
  refine ⟨σ, ⟨lt_of_le_of_ne hσ.1 (Ne.symm hσa), hσ.2⟩, ?_⟩
  have hg0 : g σ ≠ 0 := by
    intro h0
    have := hh1 σ hσ
    simp only [hh, h0, zero_mul, zero_sub, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  have he : Complex.exp ((Θ σ : ℂ) * Complex.I) = 1 := by
    rw [hσΘ]; push_cast
    have := Complex.exp_int_mul_two_pi_mul_I k
    rw [← this]; congr 1; ring
  have hgv := hgΘ σ hσ
  rw [he, mul_one] at hgv
  rw [hgv]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  exact norm_pos_iff.2 hg0

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped Real

theorem solution (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℂ) (ψ : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc a b)) (hψ : ContinuousOn ψ (Set.Icc a b))
    (hclose : ∀ σ ∈ Set.Icc a b, ‖g σ - Complex.exp ((ψ σ : ℂ) * Complex.I)‖ < 1)
    (hinc : ψ a + 3 * π ≤ ψ b) :
    ∃ σ ∈ Set.Ioc a b, 0 < (g σ).re ∧ (g σ).im = 0 :=
  FiniteEnergyPlane.exists_mem_Ioc_pos_of_norm_sub_exp_lt_aux a b hab g ψ hg hψ hclose hinc
