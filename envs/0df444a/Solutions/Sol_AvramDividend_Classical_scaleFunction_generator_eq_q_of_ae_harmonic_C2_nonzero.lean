-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T00:54:15.410457+00:00
-- url     : https://prove2.me/submissions/8bd470ea-b301-4216-92ab-7d70629b659b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_vcstar_nonzero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_harmonic_C2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Pointwise q-harmonicity of the scale function below the optimal barrier,
from almost-everywhere q-harmonicity and C2 regularity. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hbranch : W 0 = 0 ∨ X.BoundedVariation)
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 (cstar W).toReal)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 := by
  -- C2 regularity of the barrier candidate, together with the non-zero
  -- normalisation factor, gives C2 regularity of the scale function on the
  -- barrier interval.
  have hW2 : ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) :=
    scaleFunction_contDiffOn_two_of_vcstar_nonzero W hvc hk
  -- If the barrier level is zero the interval is empty and the conclusion is
  -- vacuous; otherwise the barrier level is positive, and the residual, which
  -- is continuous on the barrier interval, vanishes pointwise.
  by_cases hzero : (cstar W).toReal = 0
  · intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 0 := by
      have hx' := hx
      rw [hzero] at hx'
      exact hx'
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hx'
    exact (lt_irrefl 0 (h1.trans h2)).elim
  · have hpos : 0 < (cstar W).toReal := by
      have hnonneg : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
      exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
    exact scaleFunction_generator_eq_q_of_ae_harmonic_C2
      X hX q W hW (cstar W).toReal hpos hW2 hbranch hae
