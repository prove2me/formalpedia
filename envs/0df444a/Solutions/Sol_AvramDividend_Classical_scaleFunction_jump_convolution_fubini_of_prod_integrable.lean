-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_jump_convolution_fubini_of_prod_integrable
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:11:14.003068+00:00
-- url     : https://prove2.me/submissions/90ff8e00-a5ad-4d55-9800-590b09b85a41

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable def S189zeroLevy :
    SpectrallyNegativeLevy (Measure.dirac ()) (⊥ : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit)) where
  X := fun _ _ => 0
  c := 0
  σ := 0
  ν := 0
  isProbability := inferInstance
  σ_nonneg := le_rfl
  ν_Ici := rfl
  ν_integrable := by simp
  X_zero := fun _ => rfl
  rightCont := fun _ _ => continuousWithinAt_const
  leftLim := fun _ _ _ => ⟨0, tendsto_const_nhds⟩
  noPosJumps := fun ω t l ht hl => by
    have : (𝓝[<] t).NeBot := nhdsWithin_Iio_self_neBot' ⟨0, ht⟩
    exact (tendsto_nhds_unique hl tendsto_const_nhds).symm.le
  adapted := fun _ => measurable_const
  indepIncrements := fun s t _ => by
    rw [Indep_iff]
    intro A B _ _
    rcases Set.subsingleton_or_nontrivial A with hA | hA <;>
    rcases Set.subsingleton_or_nontrivial B with hB | hB
    all_goals first
      | (rcases hA.eq_empty_or_singleton with rfl | ⟨a, rfl⟩ <;>
         rcases hB.eq_empty_or_singleton with rfl | ⟨b, rfl⟩ <;> simp)
      | (exfalso; obtain ⟨x, -, y, -, hxy⟩ := hA; exact hxy rfl)
      | (exfalso; obtain ⟨x, -, y, -, hxy⟩ := hB; exact hxy rfl)
  stationaryIncrements := fun s t _ => by
    simp only [sub_self]; exact IdentDistrib.refl measurable_const.aemeasurable
  laplace := fun t θ _ => by
    simp [laplaceExponent]

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ)
    (hint : Integrable (Function.uncurry
      (fun x y : ℝ => Real.exp (-(θ * x)) * W (x + y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))),
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    ∫ y in Iio (0 : ℝ),
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y))) := by
  intro h
  have h1 := h S189zeroLevy Real.exp 2 (by simp [S189zeroLevy])
  have hin : ∀ y : ℝ, (∫ x in Ioi (0 : ℝ), Real.exp (-(2 * x)) * Real.exp (x + y)) = Real.exp y := by
    intro y
    have : ∀ x : ℝ, Real.exp (-(2 * x)) * Real.exp (x + y) = Real.exp y * Real.exp (-x) := by
      intro x; rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    simp_rw [this]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  simp_rw [hin] at h1
  rw [← integral_Iic_eq_integral_Iio, integral_exp_Iic_zero] at h1
  simp [S189zeroLevy] at h1
