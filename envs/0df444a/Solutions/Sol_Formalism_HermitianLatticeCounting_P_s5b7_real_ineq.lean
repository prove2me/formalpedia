-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_real_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:51.776835+00:00
-- url     : https://prove2.me/submissions/77f0b7e7-a790-44d1-a068-24d43cb37fc8

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (R t : ℝ) (hR : 0 < R) (ht : 0 ≤ t) (r d s : ℕ) (hs : s ≤ d) :
    (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        (s.factorial : ℝ) ^ r) *
      (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) ≤
    t ^ (2 * s) * R ^ (2 * (r + 1) ^ 2) * Real.pi ^ ((r + 1) * (d + 1)) /
      (s.factorial : ℝ) ^ (r + 1) := by
  have hs0 : (0 : ℝ) < (s.factorial : ℝ) := by exact_mod_cast s.factorial_pos
  have hd0 : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast d.factorial_pos
  have hsd : (s.factorial : ℝ) ≤ (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hs
  have hpi := Real.pi_pos
  have e1 : (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        (s.factorial : ℝ) ^ r) *
      (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) =
      t ^ (2 * s) * R ^ (2 * (r + 1) ^ 2) * Real.pi ^ ((r + 1) * (d + 1)) /
        ((s.factorial : ℝ) ^ r * ((d.factorial : ℝ) * ((r : ℝ) + 1))) := by
    field_simp
    ring
  rw [e1, pow_succ (s.factorial : ℝ) r]
  have h1 : (s.factorial : ℝ) ≤ (d.factorial : ℝ) * ((r : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith
  gcongr
end Formalism.HermitianLatticeCounting.P
