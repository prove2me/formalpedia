-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a250_Gaussian_HJB_factor_antitone_on_positive_reserve_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:10:44.825384+00:00
-- url     : https://prove2.me/submissions/dc137a5c-ab74-4e81-88bf-7bc65feb22fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (f fp fpp : ℝ → ℝ) (lambdaPlus lambdaMinus a y : ℝ)
    (hy : 0 < y) (hya : y ≤ a)
    (hf : ∀ t ∈ Set.Ioo 0 a, HasDerivAt f (fp t) t)
    (hfp : ∀ t ∈ Set.Ioo 0 a, HasDerivAt fp (fpp t) t)
    (hCont : ContinuousOn (fun t =>
      Real.exp (-lambdaMinus*t)*(fp t-lambdaPlus*f t))
      (Set.Icc y a))
    (hOde : ∀ t ∈ Set.Ioo 0 a,
      fpp t-(lambdaPlus+lambdaMinus)*fp t+
        lambdaPlus*lambdaMinus*f t ≤ 0) :
    Real.exp (-lambdaMinus*a)*(fp a-lambdaPlus*f a) ≤
    Real.exp (-lambdaMinus*y)*(fp y-lambdaPlus*f y) := by
  let g : ℝ → ℝ := fun t =>
    Real.exp (-lambdaMinus*t)*(fp t-lambdaPlus*f t)
  have hg (t : ℝ) (ht : t ∈ interior (Set.Icc y a)) :
      HasDerivAt g
        (Real.exp (-lambdaMinus*t)*
          (fpp t-(lambdaPlus+lambdaMinus)*fp t+
            lambdaPlus*lambdaMinus*f t)) t := by
    have ht' : t ∈ Set.Ioo y a := by
      simpa [interior_Icc] using ht
    have ht0 : t ∈ Set.Ioo (0 : ℝ) a := ⟨lt_trans hy ht'.1,ht'.2⟩
    exact avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
      f fp (fpp t) lambdaPlus lambdaMinus t
      (hf t ht0) (hfp t ht0)
  have hDif : DifferentiableOn ℝ g (interior (Set.Icc y a)) := by
    intro t ht
    exact (hg t ht).differentiableAt.differentiableWithinAt
  have hDeriv (t : ℝ) (ht : t ∈ interior (Set.Icc y a)) :
      deriv g t ≤ 0 := by
    rw [(hg t ht).deriv]
    have ht' : t ∈ Set.Ioo y a := by
      simpa [interior_Icc] using ht
    have ht0 : t ∈ Set.Ioo (0 : ℝ) a := ⟨lt_trans hy ht'.1,ht'.2⟩
    exact mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_nonneg _) (hOde t ht0)
  have hAnti : AntitoneOn g (Set.Icc y a) :=
    antitoneOn_of_deriv_nonpos (convex_Icc y a) hCont hDif hDeriv
  exact hAnti ⟨le_rfl,hya⟩ ⟨hya,le_rfl⟩ hya
