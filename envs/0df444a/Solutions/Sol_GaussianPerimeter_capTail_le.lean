-- Prove2me | solution 1 for GaussianPerimeter.capTail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:31.769306+00:00
-- url     : https://prove2.me/submissions/ae82f109-515a-4366-860f-b73a7899a776

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Theorems.Thm_GaussianPerimeter_capProfile_continuous
section
@[expose] public section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace GaussianPerimeter
private theorem capProfile_nonneg {n : ℕ} {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ capProfile n x := by
  have h := sq_le_sq' hx.1 hx.2
  exact Real.rpow_nonneg (by linarith) _
private theorem capNormalizer_nonneg (n : ℕ) : 0 ≤ capNormalizer n := by
  exact intervalIntegral.integral_nonneg (by norm_num) fun _ hx => capProfile_nonneg hx
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    capTail n t ≤ (1 - t ^ 2) ^ ((n : ℝ) / 2) / ((n : ℝ) * t * capNormalizer n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hcont := capProfile_continuous hn
  have hweighted : Continuous (fun u : ℝ => u / t * capProfile n u) :=
    (continuous_id.div_const t).mul hcont
  have hmono := intervalIntegral.integral_mono_on (μ := volume) ht' (hcont.intervalIntegrable _ _)
    (hweighted.intervalIntegrable _ _) (fun u hu => by
      have hsingle : 0 ≤ capProfile n u :=
        capProfile_nonneg ⟨by linarith [hu.1], hu.2⟩
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right ((le_div_iff₀ ht).2 (by simpa using hu.1)) hsingle :
          1 * capProfile n u ≤ _))
  let primitive (u : ℝ) := -(1 - u ^ 2) ^ ((n : ℝ) / 2) / ((n : ℝ) * t)
  have hprimitive : Continuous primitive :=
    (((continuous_const.sub (continuous_id.pow 2)).rpow_const
      (fun _ => Or.inr (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity))).neg).div_const _
  have hderiv (u : ℝ) (_ : u ∈ Ioo t 1) :
      HasDerivAt primitive (u / t * capProfile n u) u := by
    have hb := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)
    have hd := hb.rpow_const (p := (n : ℝ) / 2) (Or.inr (by linarith))
    refine (hd.neg.div_const ((n : ℝ) * t)).congr_deriv ?_
    simp only [capProfile, Pi.sub_apply]
    rw [show (n : ℝ) / 2 - 1 = ((n : ℝ) - 2) / 2 by ring]
    field_simp
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht'
    hprimitive.continuousOn hderiv (hweighted.intervalIntegrable _ _)
  rw [hFTC] at hmono
  have h1 : primitive 1 = 0 := by
    simp [primitive, Real.zero_rpow (show (n : ℝ) / 2 ≠ 0 by positivity)]
  rw [h1, zero_sub] at hmono
  simp only [primitive, neg_div, neg_neg] at hmono
  rw [capTail, ← div_div]
  exact div_le_div_of_nonneg_right hmono (capNormalizer_nonneg n)
end GaussianPerimeter
