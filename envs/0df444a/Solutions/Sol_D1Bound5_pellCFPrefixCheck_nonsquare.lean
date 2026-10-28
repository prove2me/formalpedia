-- Prove2me | solution 1 for D1Bound5.pellCFPrefixCheck_nonsquare
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:35.734983+00:00
-- url     : https://prove2.me/submissions/53773888-257f-43ad-8b1d-92285f29b49e

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions

section
namespace D1Bound5











































theorem _root_.solution {d a0 : ℤ} {N : ℕ}
    (h : pellCFPrefixCheck d a0 N = true) : ¬IsSquare d := by
  have hh : (0 ≤ a0 ∧ a0^2 < d ∧ d < (a0+1)^2) ∧
      pellCFCheckFrom d a0 (pellCFInit a0) N = true := by
    simpa only [pellCFPrefixCheck,Bool.and_eq_true,decide_eq_true_eq] using h
  rintro ⟨z,hz⟩
  have hz' : d = z^2 := by simpa only [pow_two] using hz
  have hs : |z|^2=z^2 := sq_abs z
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hlo : a0 < |z| := by nlinarith [hh.1.1,hh.1.2.1]
  have hhi : |z| < a0+1 := by nlinarith [hh.1.1,hh.1.2.2]
  omega







end D1Bound5
end
