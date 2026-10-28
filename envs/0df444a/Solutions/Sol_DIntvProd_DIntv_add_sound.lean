-- Prove2me | solution 1 for DIntvProd.DIntv.add_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:41:17.051806+00:00
-- url     : https://prove2.me/submissions/399baa4b-6ec3-4520-b52b-fd0b421c372b

import Definitions.Def_ArdaRS_Dyadic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-  DIntvDef.lean -- production-intended dyadic interval definitions + mem-soundness.

    This is the cleaner, production sibling of `Spike/DIntvMini.lean`.  It carries the
    SAME computable ops (add, mul, neg) and, crucially, PROVES that they are sound with
    respect to the real interval they denote:

        I.memR x  :=  (I.lo : ℝ) * 2^I.e ≤ x ∧ x ≤ (I.hi : ℝ) * 2^I.e

    We prove `add_sound` and `mul_sound` ONLY (the A0 remit): if `x ∈ I` and `y ∈ J`
    then `x + y ∈ I.add J` and `x * y ∈ I.mul J`.  These validate the Real-bridging
    proof style that the full A1 correctness surface will scale up.

    Design note for A1: to keep the soundness proofs clean we store BOTH endpoints at a
    COMMON exponent (add aligns to the shared exponent; mul adds exponents).  `roundTo`
    (outward widening) is a separate, monotone op whose soundness is a one-liner from
    `add`/`mul` monotonicity and is deferred to A1.

    conjecture1_proved = False.  This is finite interval arithmetic, not a proof of RH.
-/



section
namespace DIntvProd
end DIntvProd
open DIntvProd



section
namespace DIntvProd.DIntv
end DIntvProd.DIntv
open DIntvProd.DIntv









/-! ### Soundness -/




theorem solution {x y : ℝ} {I J : DIntv} (h : I.e = J.e)
    (hx : memR x I) (hy : memR y J) : memR (x + y) (add I J h) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  unfold add memR
  simp only [Int.cast_add]
  constructor
  · -- (lo_I + lo_J)·2^e ≤ x + y
    have : ((I.lo : ℝ) + (J.lo : ℝ)) * (2 : ℝ) ^ I.e
        = (I.lo : ℝ) * (2 : ℝ) ^ I.e + (J.lo : ℝ) * (2 : ℝ) ^ J.e := by
      rw [h]; ring
    rw [this]
    exact add_le_add hxlo hylo
  · -- x + y ≤ (hi_I + hi_J)·2^e
    have : ((I.hi : ℝ) + (J.hi : ℝ)) * (2 : ℝ) ^ I.e
        = (I.hi : ℝ) * (2 : ℝ) ^ I.e + (J.hi : ℝ) * (2 : ℝ) ^ J.e := by
      rw [h]; ring
    rw [this]
    exact add_le_add hxhi hyhi
