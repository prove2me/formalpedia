-- Prove2me | solution 1 for FiniteEnergyPlane.exists_contDiffOn_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T11:39:35.862039+00:00
-- url     : https://prove2.me/submissions/d2359ef0-4194-416b-8a4f-f481dfe57488

import Mathlib



/-! A `C^l` map `ρ` from an open interval to the unit circle has a `C^l` angle `θ` with
`ρ t = exp (2π i θ t)`. -/

namespace FiniteEnergyPlane

open Filter Topology MeasureTheory
open scoped ContDiff Real

theorem exists_contDiffOn_exp_eq_aux {l : ℕ} (hl : 1 ≤ l) {S : Set ℝ} (hS : IsOpen S)
    (hSc : Convex ℝ S) {ρ : ℝ → ℂ} (hρ : ContDiffOn ℝ l ρ S) (hρ1 : ∀ t ∈ S, ‖ρ t‖ = 1) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ l θ S ∧
      ∀ t ∈ S, Complex.exp (((2 * π * θ t : ℝ) : ℂ) * Complex.I) = ρ t := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨t₀, ht₀⟩
  · exact ⟨fun _ => 0, by simp [hSe], by simp [hSe]⟩
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hρ' : ContDiffOn ℝ ((m : ℕ∞ω) + 1) ρ S := by exact_mod_cast hρ
  obtain ⟨hρd, -, hρdm⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hS).1 hρ'
  have hρm : ContDiffOn ℝ m ρ S := hρ'.of_le (by exact_mod_cast Nat.le_succ m)
  have hne : ∀ t ∈ S, ρ t ≠ 0 := fun t ht h => by simpa [h] using hρ1 t ht
  set a : ℝ → ℂ := fun t => deriv ρ t * (ρ t)⁻¹ with ha
  have ham : ContDiffOn ℝ m a S := hρdm.mul (hρm.inv hne)
  have hac : ContinuousOn a S := ham.continuousOn
  have hord : S.OrdConnected := hSc.ordConnected
  set Θ : ℝ → ℂ := fun t => ∫ s in t₀..t, a s with hΘ
  have hΘd : ∀ t ∈ S, HasDerivAt Θ (a t) t := fun t ht =>
    intervalIntegral.integral_hasDerivAt_right
      ((hac.mono (hord.uIcc_subset ht₀ ht)).intervalIntegrable)
      (hac.stronglyMeasurableAtFilter hS t ht) (hac.continuousAt (hS.mem_nhds ht))
  -- `ρ · exp (-Θ)` is constant
  have hEd : ∀ t ∈ S, HasDerivAt (fun t => ρ t * Complex.exp (-Θ t)) 0 t := by
    intro t ht
    have h1 : HasDerivAt ρ (deriv ρ t) t :=
      ((hρd t ht).differentiableAt (hS.mem_nhds ht)).hasDerivAt
    have h2 : HasDerivAt (fun t => Complex.exp (-Θ t)) (Complex.exp (-Θ t) * -a t) t :=
      ((hΘd t ht).neg).cexp
    have hk : ρ t * a t = deriv ρ t := by
      show ρ t * (deriv ρ t * (ρ t)⁻¹) = deriv ρ t
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ (hne t ht), mul_one]
    have h3 := h1.mul h2
    have h4 : deriv ρ t * Complex.exp (-Θ t) + ρ t * (Complex.exp (-Θ t) * -a t) = 0 := by
      linear_combination (-Complex.exp (-Θ t)) * hk
    rw [h4] at h3
    exact h3
  have hconst : ∀ t ∈ S, ρ t * Complex.exp (-Θ t) = ρ t₀ * Complex.exp (-Θ t₀) := by
    intro t ht
    refine hS.is_const_of_deriv_eq_zero hSc.isPreconnected
      (fun s hs => (hEd s hs).differentiableAt.differentiableWithinAt) ?_ ht ht₀
    intro s hs
    exact (hEd s hs).deriv
  have hΘ0 : Θ t₀ = 0 := by simp [hΘ]
  have hρeq : ∀ t ∈ S, ρ t = ρ t₀ * Complex.exp (Θ t) := by
    intro t ht
    have := hconst t ht
    rw [hΘ0, neg_zero, Complex.exp_zero, mul_one] at this
    calc ρ t = ρ t * Complex.exp (-Θ t) * Complex.exp (Θ t) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = ρ t₀ * Complex.exp (Θ t) := by rw [this]
  have hre : ∀ t ∈ S, (Θ t).re = 0 := by
    intro t ht
    have h := congrArg norm (hρeq t ht)
    rw [norm_mul, hρ1 t ht, hρ1 t₀ ht₀, one_mul, Complex.norm_exp] at h
    have := congrArg Real.log h
    simpa using this.symm
  -- the angle
  refine ⟨fun t => (Complex.arg (ρ t₀) + (Θ t).im) / (2 * π), ?_, ?_⟩
  · have hΘc : ContDiffOn ℝ ((m : ℕ∞ω) + 1) Θ S := by
      refine (contDiffOn_succ_iff_deriv_of_isOpen hS).2 ⟨fun t ht =>
        (hΘd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      refine ham.congr fun t ht => (hΘd t ht).deriv
    have hΘc' : ContDiffOn ℝ (m + 1 : ℕ) Θ S := by exact_mod_cast hΘc
    have him : ContDiffOn ℝ (m + 1 : ℕ) (fun t => (Θ t).im) S :=
      Complex.imCLM.contDiff.comp_contDiffOn hΘc'
    exact (contDiffOn_const.add him).div_const _
  · intro t ht
    have hπ : (2 * π : ℝ) ≠ 0 := by positivity
    have e1 : 2 * π * ((Complex.arg (ρ t₀) + (Θ t).im) / (2 * π)) =
        Complex.arg (ρ t₀) + (Θ t).im := by field_simp
    rw [e1, hρeq t ht]
    have hΘi : Θ t = ((Θ t).im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre t ht]
    have hρ0 : ρ t₀ = Complex.exp ((Complex.arg (ρ t₀) : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (ρ t₀)]
      rw [hρ1 t₀ ht₀]
      simp
    calc Complex.exp (((Complex.arg (ρ t₀) + (Θ t).im : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((Complex.arg (ρ t₀) : ℂ) * Complex.I) *
            Complex.exp (((Θ t).im : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
      _ = ρ t₀ * Complex.exp (Θ t) := by rw [← hρ0, ← hΘi]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology MeasureTheory
open scoped ContDiff Real

theorem solution {l : ℕ} (hl : 1 ≤ l) {S : Set ℝ} (hS : IsOpen S)
    (hSc : Convex ℝ S) {ρ : ℝ → ℂ} (hρ : ContDiffOn ℝ l ρ S) (hρ1 : ∀ t ∈ S, ‖ρ t‖ = 1) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ l θ S ∧
      ∀ t ∈ S, Complex.exp (((2 * π * θ t : ℝ) : ℂ) * Complex.I) = ρ t :=
  exists_contDiffOn_exp_eq_aux hl hS hSc hρ hρ1
