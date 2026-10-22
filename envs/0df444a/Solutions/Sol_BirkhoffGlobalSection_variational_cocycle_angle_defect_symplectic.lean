-- Prove2me | solution 1 for BirkhoffGlobalSection.variational_cocycle_angle_defect_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T08:49:42.755209+00:00
-- url     : https://prove2.me/submissions/c94841ad-0d7b-4a52-827b-61912f4f1440

import Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_product_slit
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

open BirkhoffGlobalSection
open scoped ComplexConjugate

set_option autoImplicit false

/-- Angle defect of a symplectic period cocycle: the shifted ambient increment
agrees with the base increment up to one turn. Proved from the slit-plane
defect bound (`ambient_rotation_product_slit`, imported as a lemma) plus a
real intermediate-value argument on the shifted increment. -/
theorem solution
    (F : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hper : ∀ t : ℝ, x (t + T) = x t)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (hcocycle : ∀ t : ℝ, Y (t + T) = (Y t).comp (Y T))
    (hsymp : ∀ t : ℝ, ∀ u v : Phase,
      (Y t) u ⬝ᵥ TangentialHessian.qI.mulVec ((Y t) v) =
        u ⬝ᵥ TangentialHessian.qI.mulVec v)
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α) :
    ∀ a : ℝ, α (a + T) - α a ≤ α T - α 0 + 2 * Real.pi := by
  have hcont : Continuous α := hα.1
  have hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase := hY.1
  have hcid : ambientComplexLinearPart (ContinuousLinearMap.id ℝ Phase) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ambientComplexLinearPart, coordinateVector] <;>
      apply Complex.ext <;> simp
  have hdet0 : ambientRotationDet (Y 0) = 1 := by
    rw [hY0]
    show Matrix.det (ambientComplexLinearPart (ContinuousLinearMap.id ℝ Phase)) = 1
    rw [hcid, Matrix.det_one]
  obtain ⟨ρ₀, hρ₀, hD₀⟩ := hα.2 0
  rw [hdet0] at hD₀
  have e1 : (1 : ℂ).re = ρ₀ * Real.cos (α 0) := by rw [hD₀]
  have e2 : (1 : ℂ).im = ρ₀ * Real.sin (α 0) := by rw [hD₀]
  rw [Complex.one_re] at e1
  rw [Complex.one_im] at e2
  have hsin0 : Real.sin (α 0) = 0 := by
    have h0 : ρ₀ * Real.sin (α 0) = 0 := e2.symm
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt hρ₀)
    · exact h
  have hcos0 : 0 < Real.cos (α 0) := by
    have hne : ρ₀ ≠ 0 := ne_of_gt hρ₀
    have hcos_eq : Real.cos (α 0) = 1 / ρ₀ := by
      rw [eq_div_iff hne]
      linarith [e1]
    rw [hcos_eq]
    exact one_div_pos.mpr hρ₀
  -- `conj` is scoped notation for `starRingEnd ℂ`, so the slit bound's
  -- conjugates are already in the form the `Complex.conj_*` lemmas expect.
  set f : ℝ → ℝ := fun a => α (a + T) - α a - α T + α 0 with hf
  have hfcont : Continuous f := by
    have h1 : Continuous (fun a : ℝ => α (a + T)) :=
      hcont.comp (continuous_id.add continuous_const)
    have h2 : Continuous (fun a : ℝ => α (a + T) - α a - α T + α 0) :=
      ((h1.sub hcont).sub continuous_const).add continuous_const
    simpa only [hf] using h2
  have hf0 : f 0 = 0 := by
    have h0 : α (0 + T) - α 0 - α T + α 0 = 0 := by
      rw [zero_add]
      ring
    simpa only [hf] using h0
  -- At any point where the shifted increment reaches π, the defect is a
  -- negative real, contradicting the slit-plane bound.
  have key : ∀ c : ℝ, f c = Real.pi →
      (ambientRotationDet (Y (c + T)) * (starRingEnd ℂ) (ambientRotationDet (Y c)) *
        (starRingEnd ℂ) (ambientRotationDet (Y T))).re < 0 ∧
      (ambientRotationDet (Y (c + T)) * (starRingEnd ℂ) (ambientRotationDet (Y c)) *
        (starRingEnd ℂ) (ambientRotationDet (Y T))).im = 0 := by
    intro c hfc
    have hfc' : α (c + T) - α c - α T + α 0 = Real.pi := by
      simpa only [hf] using hfc
    have hdiff : α (c + T) - α c - α T = Real.pi - α 0 := by linarith
    obtain ⟨ρ₁, hρ₁, hD₁⟩ := hα.2 (c + T)
    obtain ⟨ρ₂, hρ₂, hD₂⟩ := hα.2 c
    obtain ⟨ρ₃, hρ₃, hD₃⟩ := hα.2 T
    have hRpos : 0 < ρ₁ * ρ₂ * ρ₃ := mul_pos (mul_pos hρ₁ hρ₂) hρ₃
    have hP_re : (ambientRotationDet (Y (c + T)) * (starRingEnd ℂ) (ambientRotationDet (Y c)) *
        (starRingEnd ℂ) (ambientRotationDet (Y T))).re
        = (ρ₁ * ρ₂ * ρ₃) * Real.cos (α (c + T) - α c - α T) := by
      simp only [hD₁, hD₂, hD₃, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Real.cos_sub, Real.sin_sub]
      ring
    have hP_im : (ambientRotationDet (Y (c + T)) * (starRingEnd ℂ) (ambientRotationDet (Y c)) *
        (starRingEnd ℂ) (ambientRotationDet (Y T))).im
        = (ρ₁ * ρ₂ * ρ₃) * Real.sin (α (c + T) - α c - α T) := by
      simp only [hD₁, hD₂, hD₃, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Real.cos_sub, Real.sin_sub]
      ring
    have hcos_eq : (ρ₁ * ρ₂ * ρ₃) * Real.cos (α (c + T) - α c - α T)
        = -((ρ₁ * ρ₂ * ρ₃) * Real.cos (α 0)) := by
      rw [hdiff, Real.cos_pi_sub]
      ring
    have hsin_eq : (ρ₁ * ρ₂ * ρ₃) * Real.sin (α (c + T) - α c - α T) = 0 := by
      rw [hdiff, Real.sin_pi_sub, hsin0, mul_zero]
    constructor
    · rw [hP_re, hcos_eq]
      have hpos : 0 < (ρ₁ * ρ₂ * ρ₃) * Real.cos (α 0) := mul_pos hRpos hcos0
      linarith
    · rw [hP_im, hsin_eq]
  have hslit_at : ∀ c : ℝ, f c = Real.pi → False := by
    intro c hfc
    have hslit := ambient_rotation_product_slit (Y c) (Y T) (hsymp c) (hsymp T)
    rw [← hcocycle c] at hslit
    obtain ⟨hre_neg, him_zero⟩ := key c hfc
    simp only [Complex.slitPlane, Set.mem_ofPred_eq] at hslit
    rcases hslit with h | h
    · linarith [hre_neg]
    · rw [him_zero] at h
      exact h rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀⟩ := hcon
  have hgt : f a₀ > 2 * Real.pi := by
    have h' : α (a₀ + T) - α a₀ - α T + α 0 > 2 * Real.pi := by
      linarith [ha₀]
    simpa only [hf] using h'
  have ha₀ne : a₀ ≠ 0 := by
    intro heq
    rw [heq, hf0] at hgt
    have hpi := Real.pi_pos
    linarith
  have hmem : Real.pi ∈ Set.Ioo (f 0) (f a₀) := by
    rw [hf0]
    exact ⟨Real.pi_pos, by linarith [hgt, Real.pi_pos]⟩
  rcases lt_or_gt_of_ne ha₀ne with hneg | hpos
  · obtain ⟨c, hcI, hfc⟩ :=
      intermediate_value_Ioo' hneg.le hfcont.continuousOn hmem
    exact hslit_at c hfc
  · obtain ⟨c, hcI, hfc⟩ :=
      intermediate_value_Ioo hpos.le hfcont.continuousOn hmem
    exact hslit_at c hfc
