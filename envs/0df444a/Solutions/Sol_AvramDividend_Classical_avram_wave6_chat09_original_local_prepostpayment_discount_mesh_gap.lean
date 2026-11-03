-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:05:59.473405+00:00
-- url     : https://prove2.me/submissions/4422439c-28db-4dd0-9a7a-65b9f2c8a768

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ) (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |w s - w t| ≤ L * |s - t|)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ∀ i < n, ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m)
    (hPre : ∀ i < n, x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ∈ Icc a b)
    (hPost : ∀ i < n, x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ∈ Icc a b) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u i : ℝ))) -
         Real.exp (-(q * (u (i + 1) : ℝ)))) *
       |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)|) ≤
      q * m * L * (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by
  have hBase := avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap D hD ω q hq u hu n m hm hmesh
  have hDmon : Monotone (fun t : ℝ≥0 => rightLimit D t ω) := avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have hCell (i : ℕ) (hi : i ∈ Finset.range n) :
      (Real.exp (-(q * (u i : ℝ))) - Real.exp (-(q * (u (i + 1) : ℝ)))) *
       |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)| ≤
      (Real.exp (-(q * (u i : ℝ))) - Real.exp (-(q * (u (i + 1) : ℝ)))) *
       (L * (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by
    have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have hd : 0 ≤ rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω :=
      sub_nonneg.mpr (hDmon hui)
    have htime : (u i : ℝ) ≤ (u (i + 1) : ℝ) := by exact_mod_cast hui
    have hqtime := mul_le_mul_of_nonneg_left htime hq
    have hclock : 0 ≤ Real.exp (-(q * (u i : ℝ))) - Real.exp (-(q * (u (i + 1) : ℝ))) :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hqtime))
    have hargs :
        (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) =
          rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω := by ring
    have hLipCell :
        |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
          w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)| ≤
        L * (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
      calc
        _ ≤ L * |(x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
            (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)| :=
              hLip _ (hPre i (Finset.mem_range.mp hi)) _ (hPost i (Finset.mem_range.mp hi))
        _ = L * (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
          rw [hargs, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left hLipCell hclock
  calc
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u i : ℝ))) -
         Real.exp (-(q * (u (i + 1) : ℝ)))) *
       |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)|) ≤
      ∑ i ∈ Finset.range n,
        (Real.exp (-(q * (u i : ℝ))) -
           Real.exp (-(q * (u (i + 1) : ℝ)))) *
        (L * (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) :=
          Finset.sum_le_sum hCell
    _ = L * (∑ i ∈ Finset.range n,
        (Real.exp (-(q * (u i : ℝ))) -
           Real.exp (-(q * (u (i + 1) : ℝ)))) *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ ≤ L * (q * m * (rightLimit D (u n) ω - rightLimit D (u 0) ω)) :=
          mul_le_mul_of_nonneg_left hBase hL
    _ = q * m * L * (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by ring