-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:11.494161+00:00
-- url     : https://prove2.me/submissions/dbeb1f7a-72ae-4df2-b5e3-2d9369c735f7

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_uniform_mass_bound_readable
import Theorems.Thm_FunctionalInequalities_Probability_zero_mem_interior_convexHull_support_of_integral_eq_zero_readable

noncomputable section
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The actual extended logarithm gives the functional bound even at zero mass.
No finite logarithm is supplied or totalized. -/
theorem FunctionalInequalities.Probability.MomentMeasure.functional_le_of_mass_bound (dx μ : Measure E) (φ : E → EReal)
    {A : ℝ} (hA : 0 < A)
    (hbound : mass dx (legendre φ) ≤ ENNReal.ofReal
      (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E)) :
    variationalFunctional dx μ φ ≤
      ((Real.log A + (Module.finrank ℝ E : ℝ) * Real.log (max (∫ x, (φ x).toReal ∂μ) 1) -
        (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) := by
  have ha : 0 < max (∫ x, (φ x).toReal ∂μ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlog := ENNReal.log_le_log hbound
  rw [ENNReal.log_ofReal_of_pos (mul_pos hA (pow_pos ha _)),
    Real.log_mul hA.ne' (pow_pos ha _).ne', Real.log_pow] at hlog
  simpa only [variationalFunctional, ← EReal.coe_sub] using
    EReal.sub_le_sub hlog (le_refl ((∫ x, (φ x).toReal ∂μ : ℝ) : EReal))
/-- The source probability, first moment, centering and full-dimensional support
produce the needed geometry. The constant is quantified before every phi;
this is new P12 coercivity support, not source Lemma15's particular constant. -/
theorem solution (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → FunctionalInequalities.Analysis.ConvexPotential φ → FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable φ μ →
      (FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre φ) ≤ ENNReal.ofReal
        (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E)) ∧
      FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ φ ≤
        ((Real.log A + (Module.finrank ℝ E : ℝ) * Real.log (max (∫ x, (φ x).toReal ∂μ) 1) -
          (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) := by
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ Set.univ = 1 := measure_univ
    simp only [hz, Measure.coe_zero, Pi.zero_apply, zero_ne_one] at hu
  have h0 := FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero_readable
    μ hμ hsub hint hbar
  obtain ⟨A, hA, hmass⟩ := FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound_readable dx μ h0
  refine ⟨A, hA, ?_⟩
  intro φ hnn hφ0 hconv hφ
  have h := hmass φ hnn hφ0 hconv hφ
  exact ⟨h, FunctionalInequalities.Probability.MomentMeasure.functional_le_of_mass_bound dx μ φ hA h⟩
