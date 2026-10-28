-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_shifted_levy_psi_analytic_on_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:13:59.352088+00:00
-- url     : https://prove2.me/submissions/f31550f4-baad-446f-ab74-74a105bcdcb6

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Topology.Closure
import Mathlib.Analysis.Analytic.Composition
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
    (φ q : ℝ) (hφ : 0 < φ) :
    AnalyticOnNhd ℝ (fun β : ℝ => X.ψ (φ + β) - q) (Set.Ioi 0) := by
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
  have hAdd : AnalyticOnNhd ℝ (fun β : ℝ => φ + β) (Set.Ioi 0) := by
    have hConst : AnalyticOnNhd ℝ (fun _ : ℝ => φ) (Set.Ioi 0) :=
      analyticOnNhd_const
    have hId : AnalyticOnNhd ℝ (fun β : ℝ => β) (Set.Ioi 0) :=
      analyticOnNhd_id
    exact AnalyticOnNhd.congr isOpen_Ioi (hConst.add hId)
      (by intro β hβ; rfl)
  have hShift : AnalyticOnNhd ℝ
      (fun β : ℝ => X.ψ (φ + β)) (Set.Ioi 0) := by
    have hComp := AnalyticOnNhd.comp hPsi hAdd (by
        intro β hβ
        exact add_pos hφ hβ)
    simpa only [Function.comp_def] using hComp
  have hConstQ : AnalyticOnNhd ℝ (fun _ : ℝ => q) (Set.Ioi 0) :=
    analyticOnNhd_const
  exact AnalyticOnNhd.congr isOpen_Ioi (hShift.sub hConstQ)
    (by intro β hβ; rfl)
