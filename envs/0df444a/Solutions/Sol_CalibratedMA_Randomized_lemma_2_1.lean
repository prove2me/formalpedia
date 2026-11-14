-- Prove2me | solution 1 for CalibratedMA.Randomized.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Aaron
-- created : 2026-11-13T18:32:10.641828+00:00
-- url     : https://prove2.me/submissions/8f6b1422-897c-4af8-9432-7961e2781ee5

import Mathlib



open MeasureTheory ProbabilityTheory

namespace CalibratedMA.Randomized.ResidualIntegrability

lemma integrable_residual {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f u v : Ω → ℝ)
    (hf : Measurable f) (hu : Measurable u) (hv : Measurable v)
    (hfbound : ∀ᵐ w ∂ν, f w ∈ Set.Icc (-1 : ℝ) 1)
    (hubound : ∀ᵐ w ∂ν, u w ∈ Set.Icc (0 : ℝ) 1)
    (hvbound : ∀ᵐ w ∂ν, v w ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun w => f w * (u w - v w)) ν := by
  apply (integrable_const (1 : ℝ)).mono' ((hf.mul (hu.sub hv)).aestronglyMeasurable)
  filter_upwards [hfbound, hubound, hvbound] with w hfw huw hvw
  have hfa : |f w| ≤ 1 := abs_le.mpr hfw
  have hdiff : |u w - v w| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [huw.1, huw.2, hvw.1, hvw.2]
  rw [Real.norm_eq_abs]
  change |f w * (u w - v w)| ≤ 1
  rw [abs_mul]
  simpa using mul_le_mul hfa hdiff (abs_nonneg (u w - v w)) (by norm_num : (0 : ℝ) ≤ 1)

lemma ae_joint_unit {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hY : ∀ᵐ w ∂μ, w.2.1 ∈ Set.Icc (0 : ℝ) 1)
    (hS : ∀ᵐ w ∂μ, w.2.2 ∈ Set.Icc (0 : ℝ) 1)
    (R : Kernel (X × ℝ) ℝ) [IsMarkovKernel R]
    (hR : ∀ xs, R xs (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    let ν : Measure ((X × ℝ × ℝ) × ℝ) :=
      μ ⊗ₘ (R.comap (fun w : X × ℝ × ℝ => (w.1, w.2.2)) (by fun_prop))
    ∀ᵐ v ∂ν, v.1.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      v.1.2.2 ∈ Set.Icc (0 : ℝ) 1 ∧ v.2 ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp only
  apply Measure.ae_compProd_of_ae_ae
  · exact (measurableSet_Icc.preimage (by fun_prop)).inter
      ((measurableSet_Icc.preimage (by fun_prop)).inter
        (measurableSet_Icc.preimage (by fun_prop)))
  · filter_upwards [hY, hS] with w hwY hwS
    have hp : ∀ᵐ p ∂(R (w.1, w.2.2)), p ∈ Set.Icc (0 : ℝ) 1 := by
      exact ae_iff.mpr (hR (w.1, w.2.2))
    change ∀ᵐ p ∂(R (w.1, w.2.2)), _
    filter_upwards [hp] with p hp
    exact ⟨hwY, hwS, hp⟩

lemma integrable_joint_residuals {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hY : ∀ᵐ w ∂μ, w.2.1 ∈ Set.Icc (0 : ℝ) 1)
    (hS : ∀ᵐ w ∂μ, w.2.2 ∈ Set.Icc (0 : ℝ) 1)
    (R : Kernel (X × ℝ) ℝ) [IsMarkovKernel R]
    (hR : ∀ xs, R xs (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (φ : X → ℝ → ℝ) (hφm : Measurable (Function.uncurry φ))
    (hφ : ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, φ x p ∈ Set.Icc (-1 : ℝ) 1) :
    let ν : Measure ((X × ℝ × ℝ) × ℝ) :=
      μ ⊗ₘ (R.comap (fun w : X × ℝ × ℝ => (w.1, w.2.2)) (by fun_prop))
    Integrable (fun v => φ v.1.1 v.2 * (v.1.2.1 - v.2)) ν ∧
      Integrable (fun v => φ v.1.1 v.2 * (v.1.2.2 - v.2)) ν ∧
      Integrable (fun v => φ v.1.1 v.2 * (v.1.2.1 - v.1.2.2)) ν := by
  let ν : Measure ((X × ℝ × ℝ) × ℝ) :=
    μ ⊗ₘ (R.comap (fun w : X × ℝ × ℝ => (w.1, w.2.2)) (by fun_prop))
  have hu := ae_joint_unit μ hY hS R hR
  have hy : ∀ᵐ v ∂ν, v.1.2.1 ∈ Set.Icc (0 : ℝ) 1 := hu.mono fun _ h => h.1
  have hs : ∀ᵐ v ∂ν, v.1.2.2 ∈ Set.Icc (0 : ℝ) 1 := hu.mono fun _ h => h.2.1
  have hp : ∀ᵐ v ∂ν, v.2 ∈ Set.Icc (0 : ℝ) 1 := hu.mono fun _ h => h.2.2
  have hf : Measurable (fun v : (X × ℝ × ℝ) × ℝ => φ v.1.1 v.2) :=
    hφm.comp (show Measurable (fun v : (X × ℝ × ℝ) × ℝ => (v.1.1, v.2)) by fun_prop)
  have hb : ∀ᵐ v ∂ν, φ v.1.1 v.2 ∈ Set.Icc (-1 : ℝ) 1 :=
    hp.mono fun v hv => hφ v.1.1 v.2 hv
  exact ⟨integrable_residual ν _ _ _ hf (by fun_prop) (by fun_prop) hb hy hp,
    integrable_residual ν _ _ _ hf (by fun_prop) (by fun_prop) hb hs hp,
    integrable_residual ν _ _ _ hf (by fun_prop) (by fun_prop) hb hy hs⟩

end CalibratedMA.Randomized.ResidualIntegrability


open MeasureTheory ProbabilityTheory

namespace CalibratedMA.Randomized.ResidualKernel

/-- Fubini for a kernel product, with a base-dependent factor pulled out of the
inner real integral. No separate integrability of the inner factor is required. -/
lemma integral_compProd_mul_base {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (f : A → B → ℝ) (g : A → ℝ)
    (hint : Integrable (fun v : A × B => f v.1 v.2 * g v.1) (μ ⊗ₘ κ)) :
    (∫ v, f v.1 v.2 * g v.1 ∂(μ ⊗ₘ κ)) =
      ∫ a, (∫ b, f a b ∂κ a) * g a ∂μ := by
  rw [Measure.integral_compProd hint]
  simp only [integral_mul_const]

/-- Conditional averaging of a test pulls the pre-postprocessing residual out
of the inner integral. -/
lemma integral_residual_pullout {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ × ℝ)) [SFinite μ]
    (R : Kernel (X × ℝ) ℝ) [IsSFiniteKernel R]
    (φ : X → ℝ → ℝ)
    (hint : Integrable
      (fun v : (X × ℝ × ℝ) × ℝ => φ v.1.1 v.2 * (v.1.2.1 - v.1.2.2))
      (μ ⊗ₘ R.comap (fun w : X × ℝ × ℝ => (w.1, w.2.2)) (by fun_prop))) :
    (∫ v, φ v.1.1 v.2 * (v.1.2.1 - v.1.2.2)
      ∂(μ ⊗ₘ R.comap (fun w : X × ℝ × ℝ => (w.1, w.2.2)) (by fun_prop))) =
      ∫ w, (∫ p, φ w.1 p ∂(R (w.1, w.2.2))) * (w.2.1 - w.2.2) ∂μ := by
  rw [Measure.integral_compProd hint]
  simp only [Kernel.comap_apply, integral_mul_const]

end CalibratedMA.Randomized.ResidualKernel

open CalibratedMA.Randomized

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure (X × ℝ × ℝ))
    [IsProbabilityMeasure μ] (hY : ∀ᵐ w ∂μ, w.2.1 ∈ Set.Icc (0 : ℝ) 1)
    (hS : ∀ᵐ w ∂μ, w.2.2 ∈ Set.Icc (0 : ℝ) 1)
    (R : Kernel (X × ℝ) ℝ) [IsMarkovKernel R] (hR : ∀ xs, R xs (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (φ : X → ℝ → ℝ) (hφm : Measurable (Function.uncurry φ))
    (hφ : ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, φ x p ∈ Set.Icc (-1 : ℝ) 1) :
    let ν : Measure ((X × ℝ × ℝ) × ℝ) :=
      μ ⊗ₘ (R.comap (fun w : X × ℝ × ℝ => (w.1, w.2.2)) (by fun_prop))
    let φup : X → ℝ → ℝ := fun x s => ∫ p, φ x p ∂(R (x, s))
    ∫ v, φ v.1.1 v.2 * (v.1.2.1 - v.2) ∂ν =
      ∫ w, φup w.1 w.2.2 * (w.2.1 - w.2.2) ∂μ + ∫ v, φ v.1.1 v.2 * (v.1.2.2 - v.2) ∂ν  := by
  dsimp only
  have hi := ResidualIntegrability.integrable_joint_residuals μ hY hS R hR φ hφm hφ
  rw [← ResidualKernel.integral_residual_pullout μ R φ hi.2.2,
    ← integral_add hi.2.2 hi.2.1]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by ring)

