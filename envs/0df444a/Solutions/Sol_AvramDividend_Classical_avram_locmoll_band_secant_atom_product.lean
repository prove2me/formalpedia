-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_secant_atom_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:19:55.501808+00:00
-- url     : https://prove2.me/submissions/b2340e17-2af8-4734-8b01-b5deceabc4f6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_cell_mass
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0)
    (g : ℝ → ℝ) (s : ℝ≥0) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℝ → ℝ := fun t => Real.exp (-(q * t)) *
      (1 - Q (riskProcess X x D t.toNNReal ω)
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω))
    F (s : ℝ) * (rightLimit D s ω - D s ω) =
      Real.exp (-(q * (s : ℝ))) *
        ((rightLimit D s ω - D s ω) + g (x + X.X s ω - rightLimit D s ω) -
          g (riskProcess X x D s ω)) := by 
  dsimp only
  rw [Real.toNNReal_coe]
  have h := avram_locmoll_band_secant_cell_mass g (riskProcess X x D s ω)
    (x + X.X s ω - rightLimit D s ω)
  have hd : riskProcess X x D s ω - (x + X.X s ω - rightLimit D s ω) =
      rightLimit D s ω - D s ω := by unfold riskProcess; ring
  rw [hd] at h
  rw [mul_assoc, sub_mul, one_mul, h]
  ring
