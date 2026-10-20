-- Prove2me | solution 1 for DerivativeChainPrivate.cubic_power_completion_from_prefix
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T11:10:52.808824+00:00
-- url     : https://prove2.me/submissions/ac6baf34-01fe-417e-9470-508808693c5d

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate







theorem chainCost_eq_sum_range {n : ℕ} (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => f i.val) =
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ := by
  unfold chainCost
  exact Fin.sum_univ_eq_sum_range (fun i => ‖f (i + 1) - f i‖) (n - 1)





end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate

theorem northeast_chain_cost (n : ℕ) (z : ℕ → ℂ)
    (hre : ∀ i < n - 1, (z i).re ≤ (z (i + 1)).re)
    (him : ∀ i < n - 1, (z i).im ≤ (z (i + 1)).im) :
    chainCost (fun i : Fin n => z i.val) ≤
      Real.sqrt 2 * ‖z (n - 1) - z 0‖ := by
  have hstep (i : ℕ) (hi : i < n - 1) :
      ‖z (i + 1) - z i‖ ≤
        ((z (i + 1)).re - (z i).re) + ((z (i + 1)).im - (z i).im) := by
    simpa only [Complex.sub_re, Complex.sub_im,
      abs_of_nonneg (sub_nonneg.mpr (hre i hi)),
      abs_of_nonneg (sub_nonneg.mpr (him i hi))] using
      Complex.norm_le_abs_re_add_abs_im (z (i + 1) - z i)
  have hsum : chainCost (fun i : Fin n => z i.val) ≤
      ((z (n - 1)).re - (z 0).re) + ((z (n - 1)).im - (z 0).im) := by
    rw [chainCost_eq_sum_range]
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1),
          (((z (i + 1)).re - (z i).re) + ((z (i + 1)).im - (z i).im)) :=
        Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
      _ = _ := by rw [Finset.sum_add_distrib,
          Finset.sum_range_sub (fun i => (z i).re),
          Finset.sum_range_sub (fun i => (z i).im)]
  apply hsum.trans
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Complex.sq_norm (z (n - 1) - z 0)
  have hdiff := sq_nonneg (((z (n - 1)).re - (z 0).re) -
    ((z (n - 1)).im - (z 0).im))
  rw [Complex.normSq_apply] at hn
  simp only [Complex.sub_re, Complex.sub_im] at hn
  have hp := mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg (z (n - 1) - z 0))
  nlinarith only [hs, hn, hdiff, hp]

theorem cubic_root_centroid_radius (u v w o : ℂ) (R : ℝ)
    (hu : ‖u - o‖ ≤ R) (hv : ‖v - o‖ ≤ R) (hw : ‖w - o‖ ≤ R) :
    ‖u - (u + v + w) / 3‖ ≤ 4 * R / 3 := by
  have heq : u - (u + v + w) / 3 =
      (2 * (u - o) - (v - o) - (w - o)) / 3 := by ring
  rw [heq, norm_div]
  have htwo : ‖(2 : ℂ) * (u - o)‖ = 2 * ‖u - o‖ := by
    rw [norm_mul]; norm_num
  have h1 := norm_sub_le ((2 : ℂ) * (u - o)) (v - o)
  have h2 := norm_sub_le ((2 : ℂ) * (u - o) - (v - o)) (w - o)
  rw [htwo] at h1
  norm_num only [Complex.norm_ofNat]
  linarith

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem power_root_inherited_derivative (q : Polynomial ℂ) (h k : ℕ)
    (z : ℂ) (hz : q.eval z = 0) (hk : k < h) :
    (Polynomial.derivative^[k] (q ^ h)).eval z = 0 := by
  obtain ⟨p, hp⟩ := Polynomial.pow_sub_dvd_iterate_derivative_pow q h k
  rw [hp, Polynomial.eval_mul, Polynomial.eval_pow, hz,
    zero_pow (show h - k ≠ 0 by omega), zero_mul]

theorem cubic_power_inherited_tail (q : Polynomial ℂ) (h : ℕ)
    (z : ℂ) (hz : q.eval z = 0) :
    ∀ m, 2 * h < m → m ≤ 3 * h →
      (Polynomial.derivative^[3 * h - m] (q ^ h)).eval z = 0 := by
  intro m hm hn
  exact power_root_inherited_derivative q h (3 * h - m) z hz (by omega)

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (q : Polynomial ℂ) (h : ℕ) (hh : 0 < h)
    (u v w o : ℂ) (R : ℝ)
    (hq : q = (Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v) *
      (Polynomial.X - Polynomial.C w))
    (hu : ‖u - o‖ ≤ R) (hv : ‖v - o‖ ≤ R) (hw : ‖w - o‖ ≤ R)
    (f : ℕ → ℂ) (hfirst : f 0 = (u + v + w) / 3)
    (hroot : ∀ i < 2 * h,
      (Polynomial.derivative^[3 * h - (i + 1)] (q ^ h)).eval (f i) = 0)
    (hre : ∀ i < 2 * h - 1, (f i).re ≤ (f (i + 1)).re)
    (him : ∀ i < 2 * h - 1, (f i).im ≤ (f (i + 1)).im)
    (hjoinre : (f (2 * h - 1)).re ≤ u.re)
    (hjoinim : (f (2 * h - 1)).im ≤ u.im) :
    ∃ z : Fin (3 * h) → ℂ,
      (∀ i, (Polynomial.derivative^[3 * h - (i.val + 1)] (q ^ h)).eval (z i) = 0) ∧
      chainCost z ≤ 4 * Real.sqrt 2 * R / 3 ∧
      (∀ i, i.val < 2 * h → z i = f i.val) ∧
      (∀ i, 2 * h ≤ i.val → z i = u) := by
  let g (i : ℕ) := if i < 2 * h then f i else u
  have hmonore (i : ℕ) (_hi : i < 3 * h - 1) : (g i).re ≤ (g (i + 1)).re := by
    by_cases ha : i + 1 < 2 * h
    · simpa only [g, if_pos ha, if_pos (show i < 2 * h by omega)] using hre i (by omega)
    · by_cases hb : i < 2 * h
      · have heq : i = 2 * h - 1 := by omega
        simp only [g, if_pos hb, if_neg ha]
        simpa only [heq] using hjoinre
      · simp only [g, if_neg hb, if_neg ha, le_refl]
  have hmonoim (i : ℕ) (_hi : i < 3 * h - 1) : (g i).im ≤ (g (i + 1)).im := by
    by_cases ha : i + 1 < 2 * h
    · simpa only [g, if_pos ha, if_pos (show i < 2 * h by omega)] using him i (by omega)
    · by_cases hb : i < 2 * h
      · have heq : i = 2 * h - 1 := by omega
        simp only [g, if_pos hb, if_neg ha]
        simpa only [heq] using hjoinim
      · simp only [g, if_neg hb, if_neg ha, le_refl]
  have hqu : q.eval u = 0 := by simp [hq]
  refine ⟨fun i => g i.val, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < 2 * h
    · simpa only [g, if_pos hi] using hroot i.val hi
    · simp only [g, if_neg hi]
      exact cubic_power_inherited_tail q h u hqu (i.val + 1) (by omega) (by omega)
  · have hcost := northeast_chain_cost (3 * h) g hmonore hmonoim
    have hlast : g (3 * h - 1) = u := by simp only [g, if_neg (show ¬3 * h - 1 < 2 * h by omega)]
    have hstart : g 0 = (u + v + w) / 3 := by
      simpa only [g, if_pos (show 0 < 2 * h by omega)] using hfirst
    rw [hlast, hstart] at hcost
    exact hcost.trans ((mul_le_mul_of_nonneg_left
      (cubic_root_centroid_radius u v w o R hu hv hw) (Real.sqrt_nonneg 2)).trans_eq (by ring))
  · intro i hi
    exact if_pos hi
  · intro i hi
    exact if_neg (by omega)
