-- Prove2me | solution 1 for D1Bound5.pellCFSolutions_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:16.6313+00:00
-- url     : https://prove2.me/submissions/ef7ec87b-231a-4987-b7b5-fd1961731d75

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions
import Theorems.Thm_D1Bound5_pellCFAt_mem_trace
import Theorems.Thm_D1Bound5_pellCFPrefixCheck_nonsquare
import Theorems.Thm_D1Bound5_pellCFPrefixCheck_pairs
import Theorems.Thm_D1Bound5_pell_norm_two_bounded_prefix

section
namespace D1Bound5















































/-- A finite checked continued-fraction computation contains every positive
norm-two solution below its stopping numerator. The output list is the
actual filtered trace of the integer algorithm. -/
theorem _root_.solution {d a0 X x y : ℤ} {N : ℕ}
    (hd : 7 ≤ d) (hcheck : pellCFPrefixCheck d a0 N = true)
    (hstop : X < (pellCFAt d a0 (pellCFInit a0) N).p)
    (hx : 0 < x) (hy : 0 < y) (heq : x^2-d*y^2=2) (hX : x ≤ X) :
    (x,y) ∈ pellCFSolutions d a0 X N := by
  have hpairs := pellCFPrefixCheck_pairs hcheck
  have hstop' : X < (pellConvergentPair (Real.sqrt (d : ℝ)) N).1 := by
    simpa only [hpairs N le_rfl,Prod.fst] using hstop
  obtain ⟨i,hi,hxy⟩ := pell_norm_two_bounded_prefix hd
    (pellCFPrefixCheck_nonsquare hcheck) hx hy heq hX hstop'
  have hpair : ((pellCFAt d a0 (pellCFInit a0) i).p,
      (pellCFAt d a0 (pellCFInit a0) i).q) = (x,y) :=
    (hpairs i hi.le).symm.trans hxy
  obtain ⟨hp,hq⟩ := Prod.mk.inj hpair
  apply List.mem_filterMap.mpr
  refine ⟨pellCFAt d a0 (pellCFInit a0) i,
    pellCFAt_mem_trace d a0 (pellCFInit a0) hi.le, ?_⟩
  simp [hp,hq,hx,hy,hX,heq]



end D1Bound5
end
