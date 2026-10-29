-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T21:52:28.200479+00:00
-- url     : https://prove2.me/submissions/df1450d7-3062-43b9-93ed-c612f5e1fc23

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Topology.Closure
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (y : ℝ) (hy : 0 < y) :
    ∃ m : ℝ, HasDerivAt X.ψ m y := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let Z : Ω → ℝ := fun ω => X.X 1 ω
  have hInt : ∀ θ : ℝ, 0 < θ →
      Integrable (fun ω : Ω => Real.exp (θ * Z ω)) P := by
    intro θ hθ
    simpa only [Z] using (X.laplace 1 θ hθ.le).1
  have hSubset : (Set.Ioi (0 : ℝ)) ⊆ integrableExpSet Z P := by
    intro θ hθ
    exact hInt θ hθ
  have hInterior : Set.Ioi (0 : ℝ) ⊆
      interior (integrableExpSet Z P) :=
    isOpen_Ioi.subset_interior_iff.mpr hSubset
  have hCgf : AnalyticOnNhd ℝ (cgf Z P) (Set.Ioi 0) :=
    (analyticOnNhd_cgf (X := Z) (μ := P)).mono hInterior
  have hEq : Set.EqOn (cgf Z P) X.ψ (Set.Ioi 0) := by
    intro θ hθ
    change Real.log (∫ ω : Ω, Real.exp (θ * Z ω) ∂P) = X.ψ θ
    have hLap : (∫ ω : Ω, Real.exp (θ * Z ω) ∂P) =
        Real.exp (X.ψ θ) := by
      simpa only [Z, one_mul, NNReal.coe_one, SpectrallyNegativeLevy.ψ]
        using (X.laplace 1 θ hθ.le).2
    rw [hLap, Real.log_exp]
  have hPsi : AnalyticOnNhd ℝ X.ψ (Set.Ioi 0) :=
    AnalyticOnNhd.congr isOpen_Ioi hCgf hEq
  exact ⟨deriv X.ψ y, (hPsi y hy).differentiableAt.hasDerivAt⟩
