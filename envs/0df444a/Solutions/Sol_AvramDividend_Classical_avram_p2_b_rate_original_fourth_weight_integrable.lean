-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:42:47.60048+00:00
-- url     : https://prove2.me/submissions/ef615dc8-4967-4626-8fb8-23164fbc1e28

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable
      (fun ω => (Real.exp (θ * X.X t ω) - 1) ^ 4) P := by
  let Z : Ω → ℝ := fun ω => Real.exp (θ * X.X t ω)
  have hExp (n : ℕ) : Integrable (fun ω => (Z ω) ^ n) P := by
    have hn : 0 ≤ (n : ℝ) * θ :=
      mul_nonneg (Nat.cast_nonneg n) hθ
    have hi := (X.laplace t ((n : ℝ) * θ) hn).1
    have heq :
        (fun ω : Ω => (Z ω) ^ n) =
          (fun ω : Ω => Real.exp (((n : ℝ) * θ) * X.X t ω)) := by
      funext ω
      dsimp [Z]
      calc
        (Real.exp (θ * X.X t ω)) ^ n =
            Real.exp ((n : ℝ) * (θ * X.X t ω)) := by
              symm
              exact Real.exp_nat_mul (θ * X.X t ω) n
        _ = Real.exp (((n : ℝ) * θ) * X.X t ω) := by ring
    rwa [heq]
  have hpoly :=
    ((((hExp 4).sub ((hExp 3).const_mul (4 : ℝ))).add
      ((hExp 2).const_mul (6 : ℝ))).sub
      ((hExp 1).const_mul (4 : ℝ))).add (hExp 0)
  refine hpoly.congr (Filter.Eventually.of_forall (fun ω => ?_))
  dsimp [Z]
  ring