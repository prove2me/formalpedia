-- Prove2me | solution 1 for BoundedNV.Pooling.lemma1_affine_invariance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:44:34.46934+00:00
-- url     : https://prove2.me/submissions/e25b7ec0-851b-4669-a0e8-74cef372fea0

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Logit
set_option autoImplicit false
open MeasureTheory BoundedNV.Pooling

theorem BNP_cov (g : ℝ → ℝ) (a d : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, g (a * x + d) = a⁻¹ * ∫ v : ℝ, g v := by
  have h1 : ∫ x : ℝ, g (a * x + d) = ∫ x : ℝ, (fun w => g (w + d)) (a * x) := by
    rfl
  rw [h1, Measure.integral_comp_mul_left (fun w => g (w + d)) a, integral_add_right_eq_self g d]
  rw [abs_of_pos (inv_pos.2 ha)]
  simp

theorem solution (Y : Set ℝ) (u : ℝ → ℝ) (β a d : ℝ)
    (hY : MeasurableSet Y)
    (hu : IntegrableOn (fun v => Real.exp (u v / β)) Y)
    (hZ : 0 < ∫ v in Y, Real.exp (u v / β))
    (hβ : 0 < β) (ha : 0 < a) (y : ℝ) :
    logitCDF ((fun v : ℝ => a * v + d) '' Y)
        (fun z => u ((z - d) / a)) β (a * y + d) =
      logitCDF Y u β y := by
  set T : Set ℝ := (fun v : ℝ => a * v + d) '' Y with hTdef
  have hmem : ∀ x : ℝ, (a * x + d ∈ T ↔ x ∈ Y) := by
    intro x
    constructor
    · rintro ⟨v, hv, hvx⟩
      have : v = x := by
        have := hvx; simp only at this
        nlinarith [ha]
      rwa [← this]
    · intro hx; exact ⟨x, hx, rfl⟩
  have hTeq : T = (fun w => (w - d) / a) ⁻¹' Y := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      simp only [Set.mem_preimage]
      have : (a * v + d - d) / a = v := by field_simp; ring
      rw [this]; exact hv
    · intro hw
      refine ⟨(w - d) / a, hw, ?_⟩
      simp only; field_simp; ring
  have hT : MeasurableSet T := by
    rw [hTeq]; exact hY.preimage (by fun_prop)
  set F : ℝ → ℝ := fun w => Real.exp (u ((w - d) / a) / β) with hF
  have hZT : ∫ w in T, F w = a * ∫ v in Y, Real.exp (u v / β) := by
    rw [← integral_indicator hT, ← integral_indicator hY]
    have e1 : ∀ x : ℝ, T.indicator F (a * x + d) = Y.indicator (fun v => Real.exp (u v / β)) x := by
      intro x
      by_cases hx : x ∈ Y
      · rw [Set.indicator_of_mem ((hmem x).2 hx), Set.indicator_of_mem hx]
        simp only [hF]
        have : (a * x + d - d) / a = x := by field_simp; ring
        rw [this]
      · rw [Set.indicator_of_notMem (fun h => hx ((hmem x).1 h)), Set.indicator_of_notMem hx]
    have := BNP_cov (T.indicator F) a d ha
    simp only [e1] at this
    rw [this]
    field_simp
  unfold logitCDF
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  have hcov := BNP_cov ((Set.Iic (a * y + d)).indicator (logitDensity T (fun z => u ((z - d) / a)) β)) a d ha
  have hpt : ∀ x : ℝ, (Set.Iic (a * y + d)).indicator (logitDensity T (fun z => u ((z - d) / a)) β) (a * x + d) =
      a⁻¹ * (Set.Iic y).indicator (logitDensity Y u β) x := by
    intro x
    have hle : a * x + d ∈ Set.Iic (a * y + d) ↔ x ∈ Set.Iic y := by
      simp only [Set.mem_Iic]
      constructor <;> intro h <;> nlinarith
    by_cases hx : x ∈ Set.Iic y
    · rw [Set.indicator_of_mem (hle.2 hx), Set.indicator_of_mem hx]
      unfold logitDensity
      by_cases hxY : x ∈ Y
      · rw [Set.indicator_of_mem ((hmem x).2 hxY), Set.indicator_of_mem hxY]
        have : (a * x + d - d) / a = x := by field_simp; ring
        simp only [this]
        rw [hZT]
        field_simp
      · rw [Set.indicator_of_notMem (fun h => hxY ((hmem x).1 h)), Set.indicator_of_notMem hxY]
        simp
    · rw [Set.indicator_of_notMem (fun h => hx (hle.1 h)), Set.indicator_of_notMem hx]
      simp
  simp only [hpt] at hcov
  rw [integral_const_mul] at hcov
  exact (mul_left_cancel₀ (inv_ne_zero ha.ne') hcov).symm

