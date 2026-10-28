-- Prove2me | solution 1 for D1Bound5.pellCFSolutions_complete_abs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:25.896205+00:00
-- url     : https://prove2.me/submissions/234824c6-ccef-4ee8-971e-2c1264d55152

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Theorems.Thm_D1Bound5_pellCFSolutions_complete

section
namespace D1Bound5

















































/-- This is the cutoff used for the signed rational extensions: their
magnitude is u^2-1, and the bound is X^2. Both Pell signs are retained via
absolute values; no positivity assumption on the supplied roots is made. -/
theorem _root_.solution {d a0 X u v : ℤ} {N : ℕ}
    (hd : 7 ≤ d) (hcheck : pellCFPrefixCheck d a0 N = true)
    (hstop : X < (pellCFAt d a0 (pellCFInit a0) N).p)
    (hX : 1 ≤ X) (hv : v ≠ 0) (heq : u^2-d*v^2=2)
    (hbound : u^2-1 ≤ X^2) :
    (|u|,|v|) ∈ pellCFSolutions d a0 X N := by
  have hu : u ≠ 0 := by
    intro hu
    rw [hu] at heq
    have hprod : 0 ≤ d*v^2 := mul_nonneg (by omega) (sq_nonneg v)
    nlinarith
  have hupos : 0 < |u| := abs_pos.mpr hu
  have hvpos : 0 < |v| := abs_pos.mpr hv
  have huX : |u| ≤ X := by
    by_contra h
    have hle : X+1 ≤ |u| := by omega
    nlinarith [sq_abs u]
  apply pellCFSolutions_complete hd hcheck hstop hupos hvpos _ huX
  simpa only [sq_abs] using heq

end D1Bound5
end
