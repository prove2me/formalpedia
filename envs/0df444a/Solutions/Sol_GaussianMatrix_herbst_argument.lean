-- Prove2me | solution 1 for GaussianMatrix.herbst_argument
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T04:27:10.819212+00:00
-- url     : https://prove2.me/submissions/f0a1aca7-72c1-4eb9-9a1c-5586b40b77e6

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (c : ℝ) (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * f ω)) μ)
    (hent : ∀ s : ℝ, 0 < s →
      ∫ ω, s * f ω * Real.exp (s * f ω) ∂μ
        - (∫ ω, Real.exp (s * f ω) ∂μ) * Real.log (∫ ω, Real.exp (s * f ω) ∂μ)
        ≤ c * s ^ 2 * ∫ ω, Real.exp (s * f ω) ∂μ)
    (s : ℝ) (hs : 0 ≤ s) :
    ∫ ω, Real.exp (s * f ω) ∂μ ≤ Real.exp (s * ∫ ω, f ω ∂μ + c * s ^ 2) := by
  set M : ℝ → ℝ := mgf f μ with hMdef
  set E : ℝ := ∫ ω, f ω ∂μ with hEdef
  have hint' : ∀ u : ℝ, u ∈ interior (integrableExpSet f μ) := by
    intro u
    have : integrableExpSet f μ = Set.univ := Set.eq_univ_of_forall fun v => hint v
    simp [this]
  set M' : ℝ → ℝ := fun u => ∫ ω, f ω * Real.exp (u * f ω) ∂μ with hM'def
  have hM : ∀ u, HasDerivAt M (M' u) u := fun u => hasDerivAt_mgf (hint' u)
  have hMpos : ∀ u, 0 < M u := fun u => mgf_pos (hint u)
  have hMeq : ∀ u, ∫ ω, Real.exp (u * f ω) ∂μ = M u := fun u => rfl
  -- G u = log M u - u E - c u²
  set G : ℝ → ℝ := fun u => Real.log (M u) - u * E - c * u ^ 2 with hGdef
  set G' : ℝ → ℝ := fun u => M' u / M u - E - c * (2 * u) with hG'def
  have hG : ∀ u, HasDerivAt G (G' u) u := by
    intro u
    have h1 := (hM u).log (hMpos u).ne'
    have h2 := (hasDerivAt_id u).mul_const E
    have h3 := ((hasDerivAt_pow 2 u).const_mul c)
    have := (h1.sub h2).sub h3
    refine HasDerivAt.congr_deriv (f := G) this ?_
    simp only [hG'def]
    ring
  have hG0 : G 0 = 0 := by simp [hGdef, hMdef]
  have hG'0 : G' 0 = 0 := by
    simp [hG'def, hM'def, hMdef, hEdef]
  -- φ u = G u / u is antitone on (0, ∞)
  set φ : ℝ → ℝ := fun u => G u / u with hφdef
  have hφ : ∀ u, 0 < u → HasDerivAt φ ((G' u * u - G u * 1) / u ^ 2) u := by
    intro u hu
    exact (hG u).div (hasDerivAt_id u) hu.ne'
  have hnum : ∀ u, 0 < u → G' u * u - G u * 1 ≤ 0 := by
    intro u hu
    have he := hent u hu
    rw [hMeq] at he
    have hfe : ∫ ω, u * f ω * Real.exp (u * f ω) ∂μ = u * M' u := by
      simp_rw [mul_assoc]; rw [integral_const_mul]
    rw [hfe] at he
    have hMu := hMpos u
    have key : u * (M' u / M u) - Real.log (M u) ≤ c * u ^ 2 := by
      have : u * (M' u / M u) - Real.log (M u) = (u * M' u - M u * Real.log (M u)) / M u := by
        field_simp
      rw [this, div_le_iff₀ hMu]; linarith
    simp only [hG'def, hGdef]
    nlinarith [key]
  have hanti : AntitoneOn φ (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro u hu
      exact (hφ u hu).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      intro u hu
      exact (hφ u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro u hu
      rw [(hφ u hu).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (hnum u hu) (sq_nonneg _)
  -- conclude
  rcases hs.eq_or_lt with hs0 | hspos
  · subst hs0
    simp only [zero_mul, Real.exp_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero]
    simp
  have hslope := (hG 0).tendsto_slope_zero_right
  rw [hG'0] at hslope
  have hφs : φ s ≤ 0 := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT hspos] with u hu
    simp only [zero_add, hG0, sub_zero, smul_eq_mul]
    rw [inv_mul_eq_div]
    exact hanti hu.1 hspos hu.2.le
  have hGs : G s ≤ 0 := by
    have : G s = φ s * s := by simp [hφdef, hspos.ne']
    rw [this]; exact mul_nonpos_of_nonpos_of_nonneg hφs hs
  rw [hMeq]
  have hlog : Real.log (M s) ≤ s * E + c * s ^ 2 := by simp only [hGdef] at hGs; linarith
  calc M s = Real.exp (Real.log (M s)) := (Real.exp_log (hMpos s)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog
