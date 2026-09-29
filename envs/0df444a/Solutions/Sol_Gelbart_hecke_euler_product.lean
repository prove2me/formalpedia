-- Prove2me | solution 1 for Gelbart.hecke_euler_product
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T23:11:44.2126+00:00
-- url     : https://prove2.me/submissions/f0eb771b-5ff0-47d2-91b6-5f65feab3595

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_Gelbart_hecke_series

namespace Gelbart

theorem hecke_euler_product
    (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hgrowth : HeckeCoeffGrowth a c)
    (h1 : a 1 = 1) (hmul : ∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n)
    {s : ℂ} (hs : c + 1 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∏ p ∈ (Finset.range N).filter Nat.Prime,
        ∑' m : ℕ, a (p ^ m) / (p : ℂ) ^ ((m : ℂ) * s))
      Filter.atTop (nhds (LSeries a s)) := by
  classical
  have hsum : LSeriesSummable a s := by
    apply LSeriesSummable_of_le_const_mul_rpow hs
    obtain ⟨K, hK⟩ := hgrowth
    refine ⟨K, fun n hn => ?_⟩
    simpa only [add_sub_cancel_right] using hK n (Nat.one_le_iff_ne_zero.mpr hn)
  have hterm1 : LSeries.term a s 1 = 1 := by simp [LSeries.term, h1]
  have htermmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      LSeries.term a s (m * n) = LSeries.term a s m * LSeries.term a s n := by
    intro m n hmn
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [LSeries.term_of_ne_zero (mul_ne_zero hm hn),
      LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn, hmul m n hmn,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow, div_mul_div_comm]
  have h := EulerProduct.eulerProduct hterm1 htermmul hsum.norm (LSeries.term_zero a s)
  have hlocal (p : ℕ) (hp : p.Prime) :
      (∑' m : ℕ, LSeries.term a s (p ^ m)) =
        ∑' m : ℕ, a (p ^ m) / (p : ℂ) ^ ((m : ℂ) * s) := by
    apply tsum_congr
    intro m
    rw [LSeries.term_of_ne_zero (pow_ne_zero m hp.ne_zero)]
    simp only [Nat.cast_pow, Complex.natCast_cpow_natCast_mul]
  convert h using 1
  · funext N
    apply Finset.prod_congr
    · rfl
    intro p hp
    exact (hlocal p (Finset.mem_filter.mp hp).2).symm
  · rfl

end Gelbart

theorem solution
    (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hgrowth : Gelbart.HeckeCoeffGrowth a c)
    (h1 : a 1 = 1) (hmul : ∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n)
    {s : ℂ} (hs : c + 1 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∏ p ∈ (Finset.range N).filter Nat.Prime,
        ∑' m : ℕ, a (p ^ m) / (p : ℂ) ^ ((m : ℂ) * s))
      Filter.atTop (nhds (LSeries a s)) :=
  Gelbart.hecke_euler_product a c hc hgrowth h1 hmul hs

#print axioms Gelbart.hecke_euler_product
#print axioms solution
