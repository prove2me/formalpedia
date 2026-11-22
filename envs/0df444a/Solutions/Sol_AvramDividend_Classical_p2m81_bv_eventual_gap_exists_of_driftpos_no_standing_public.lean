-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_eventual_gap_exists_of_driftpos_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T13:42:43.12434+00:00
-- url     : https://prove2.me/submissions/b64ce14b-4d74-43a4-82ae-dec4aec1ce1a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hdrift : 0 < X.drift)
    (hlim : Tendsto (fun n : ℕ => ∫ y : ℝ,
        (Real.exp (((n : ℝ) + 1) * y) - 1 - ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)
        ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) atTop
      (nhds (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))) :
    ∃ N : ℕ,
      (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) -
          (X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)))) / 4 <
        (∫ y : ℝ, (Real.exp (((N : ℝ) + 1) * y) - 1 - ((N : ℝ) + 1) * y) /
          ((N : ℝ) + 1) ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) ∧
      q / ((N : ℝ) + 1) < (X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)))) / 4 ∧
      (∫ _ in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) / ((N : ℝ) + 1) <
        (X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)))) / 4 := by
  let A := ∫ y in Ioo (-1 : ℝ) 0, |y| ∂X.ν
  let B := ∫ _ in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν
  let J (n : ℕ) := ∫ y in Ioo (-1 : ℝ) 0,
    (Real.exp (((n : ℝ) + 1) * y) - 1 - ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂X.ν
  let ε := (X.c + A) / 4
  have hA : A = -(∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) := calc
    A = ∫ y in Ioo (-1 : ℝ) 0, -y ∂X.ν :=
      setIntegral_congr_fun measurableSet_Ioo (fun _ hy => abs_of_neg hy.2)
    _ = _ := integral_neg _
  have hε : 0 < ε := by
    change 0 < (X.c + A) / 4
    rw [hA, ← sub_eq_add_neg]
    exact div_pos hdrift (by norm_num)
  have hJ : ∀ᶠ n in atTop, A - ε < J n :=
    hlim.eventually (lt_mem_nhds (sub_lt_self A hε))
  have hfrac (C : ℝ) : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  have hq := (hfrac q).eventually (gt_mem_nhds hε)
  have hB := (hfrac B).eventually (gt_mem_nhds hε)
  change ∃ N : ℕ, A - ε < J N ∧ q / ((N : ℝ) + 1) < ε ∧ B / ((N : ℝ) + 1) < ε
  exact (hJ.and (hq.and hB)).exists
