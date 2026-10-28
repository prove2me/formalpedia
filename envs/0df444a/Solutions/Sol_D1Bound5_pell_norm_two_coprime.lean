-- Prove2me | solution 1 for D1Bound5.pell_norm_two_coprime
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:21.004324+00:00
-- url     : https://prove2.me/submissions/688caf69-6320-4549-95dc-b3f93ef2404f

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

section
namespace D1Bound5

















theorem _root_.solution {d x y : ℤ} (hx : 0 < x)
    (heq : x^2-d*y^2=2) : IsCoprime x y := by
  let g : ℤ := Int.gcd x y
  obtain ⟨u,hu⟩ := Int.gcd_dvd_left x y
  obtain ⟨v,hv⟩ := Int.gcd_dvd_right x y
  change x = g*u at hu
  change y = g*v at hv
  have hg0 : g ≠ 0 := by
    intro hg
    have : x = 0 := by simpa only [hg, zero_mul] using hu
    omega
  have hgpos : 0 < g := lt_of_le_of_ne (Int.natCast_nonneg _) hg0.symm
  have hdiv : g^2 ∣ (2 : ℤ) := by
    refine ⟨u^2-d*v^2, ?_⟩
    rw [← heq,hu,hv]
    ring
  have hbound : g^2 ≤ 2 := Int.le_of_dvd (by norm_num) hdiv
  have hg1 : g = 1 := by nlinarith
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change (Int.gcd x y : ℤ) = 1 at hg1
  exact_mod_cast hg1





end D1Bound5
end
