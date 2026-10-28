-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exp_process_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:01:37.986125+00:00
-- url     : https://prove2.me/submissions/1c072623-b3c7-4878-9ad3-fd1d0033d4fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) (t : ℝ≥0) :
    Integrable (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) P := by
  obtain ⟨hint_t, -⟩ := X.laplace t θ hθ
  have e1 : (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))
      = fun ω => (Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ))⁻¹
        * Real.exp (θ * X.X t ω) := by
    funext ω
    rw [Real.exp_sub, div_eq_inv_mul]
  rw [e1]
  exact hint_t.const_mul _
