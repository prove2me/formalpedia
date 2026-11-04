-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_integer_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:27:34.358797+00:00
-- url     : https://prove2.me/submissions/3c93f274-9b48-4300-9e46-9bc48a5fd98e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
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
    (t : ℝ≥0) (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable
      (fun ω => (Real.exp (θ * X.X t ω)) ^ k *
        (Real.exp (θ * X.X t ω) - 1) ^ 4) P := by
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
    ((((hExp (k + 4)).sub ((hExp (k + 3)).const_mul (4 : ℝ))).add
      ((hExp (k + 2)).const_mul (6 : ℝ))).sub
      ((hExp (k + 1)).const_mul (4 : ℝ))).add (hExp k)
  refine hpoly.congr (Filter.Eventually.of_forall (fun ω => ?_))
  dsimp [Z]
  simp only [pow_add]
  ring
