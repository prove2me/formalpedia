-- Prove2me | solution 1 for AvramDividend.Classical.original_purejump_positive_esscher_killed_potential_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:51:24.000108+00:00
-- url     : https://prove2.me/submissions/4010cb7f-7424-43a7-9eb3-cfed23f90df8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_original_purejump_esscher_kernel_Bernstein_package
import Theorems.Thm_AvramDividend_Classical_killed_bernstein_infinite_activity_potential_ac
import Theorems.Thm_AvramDividend_Classical_original_purejump_esscher_killed_Bernstein_lower
import Theorems.Thm_AvramDividend_Classical_positive_support_laplace_real_from_finite_lintegral
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (φ : ℝ) (hφ : 0 < φ) (hψ : 0 < X.ψ φ) :
    ∃ U : Measure ℝ,
      U (Iic (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, U {x} = 0) ∧
      U Set.univ = ENNReal.ofReal (φ / X.ψ φ) ∧
      (∀ s : ℝ, 0 < s →
        IntegrableOn (fun y : ℝ => Real.exp (-(s * y))) (Ioi 0) U ∧
        ∫ y in Ioi (0 : ℝ),
          Real.exp (-(s * y)) ∂U =
            (φ + s) / X.ψ (φ + s)) := by
  obtain ⟨κ, k, hκdef, hκsf, hkDef, hkPos,
      hκsupp, hκac, hκinf, hKernel⟩ :=
    original_purejump_esscher_kernel_Bernstein_package
      X hX hBV hσ φ hφ hψ
  letI : SFinite κ := hκsf
  have hKFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ,
        ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤ :=
    fun s hs => (hKernel s hs).1
  obtain ⟨U, hUIic, hUAc, hUAtoms, hUMass, hULap⟩ :=
    killed_bernstein_infinite_activity_potential_ac
      κ hκsupp k hkPos hKFin hκac hκinf
  have hMass : U Set.univ = ENNReal.ofReal (φ / X.ψ φ) := by
    simpa only [hkDef, inv_div] using hUMass
  refine ⟨U, hUIic, hUAtoms, hMass, ?_⟩
  intro s hs
  have hRpos := (original_purejump_esscher_killed_Bernstein_lower
    X hX hσ φ hφ hψ s hs.le).2
  have hc : 0 ≤ (φ + s) / X.ψ (φ + s) := by
    simpa only [inv_div] using (inv_nonneg.mpr hRpos.le)
  have hLap : (∫⁻ y : ℝ,
      ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
        ENNReal.ofReal ((φ + s) / X.ψ (φ + s)) :=
    (hULap s hs).trans (hKernel s hs).2.symm
  exact positive_support_laplace_real_from_finite_lintegral
    U hUIic s ((φ + s) / X.ψ (φ + s)) hs hc hLap
