-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e2_original_compact_discounted_HJB_integrand_uniform_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:30:41.461114+00:00
-- url     : https://prove2.me/submissions/b64b8368-18f0-4cce-b6b3-bed61a81db33

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (hwMeas : Measurable w)
(q : ℝ) (hq : 0 ≤ q) (a b L R A : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
(hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
(hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
 |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(hDeriv : ∀ y ∈ Icc a b, |deriv w y| ≤ A)
(E : ℕ → Set (ℝ≥0 × Ω))
(hEregion : ∀ n, ∀ p ∈ E n,
 Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b) :
∃ K : ℝ, 0 ≤ K ∧ ∀ n (p : ℝ≥0 × Ω),
 |(if p ∈ E n then Real.exp (-(q * (p.1 : ℝ))) *
   (X.drift * deriv w (Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
    (∫ z in Iio (0 : ℝ),
      w (Function.leftLim
         (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
      w (Function.leftLim
         (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
    q * w (Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
 else 0)| ≤ K := by
  obtain ⟨K, hK, hBound⟩ :=
    avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
      X hBV w hwMeas q a b L R A
      ha ha2 hab hL hR hA hLip hWbound hDeriv
  refine ⟨K, hK, ?_⟩
  intro n p
  by_cases hp : p ∈ E n
  · simp only [if_pos hp]
    have ht : 0 ≤ (p.1 : ℝ) := by positivity
    have hExp : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
      have hprod : 0 ≤ q * (p.1 : ℝ) := mul_nonneg hq ht
      calc
        Real.exp (-(q * (p.1 : ℝ))) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr hprod)
        _ = 1 := Real.exp_zero
    have hExpNonneg : 0 ≤ Real.exp (-(q * (p.1 : ℝ))) :=
      (Real.exp_pos _).le
    rw [abs_mul, abs_of_nonneg hExpNonneg]
    calc
      Real.exp (-(q * (p.1 : ℝ))) * _ ≤ 1 * _ :=
        mul_le_mul_of_nonneg_right hExp (abs_nonneg _)
      _ ≤ K := by simpa only [one_mul] using hBound _ (hEregion n p hp)
  · simpa only [if_neg hp, abs_zero] using hK