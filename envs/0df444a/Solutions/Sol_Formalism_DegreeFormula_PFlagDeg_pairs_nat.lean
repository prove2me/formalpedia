-- Prove2me | solution 1 for Formalism.DegreeFormula.PFlagDeg.pairs_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:09.847923+00:00
-- url     : https://prove2.me/submissions/a135febe-8adb-425c-a5d9-406390ff8dce

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg
namespace Formalism.DegreeFormula.PFlagDeg
theorem _root_.solution (N : ℕ) :
    ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) = (sfac N : ℝ) := by
  rw [Finset.prod_comm]
  unfold sfac
  push_cast
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : ∀ i : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) =
      (fun m : ℕ => if m < (k : ℕ) then (((k : ℕ) : ℝ) - (m : ℝ)) else 1) (i : ℕ) := fun i => rfl
  rw [Finset.prod_congr rfl (fun i _ => h1 i),
    Fin.prod_univ_eq_prod_range (fun m : ℕ => if m < (k : ℕ) then (((k : ℕ) : ℝ) - (m : ℝ)) else 1) N,
    ← Finset.prod_range_mul_prod_Ico _ (le_of_lt k.2)]
  rw [Finset.prod_eq_one (s := Finset.Ico (k : ℕ) N)
    (fun i hi => by rw [Finset.mem_Ico] at hi; simp [not_lt.mpr hi.1]), mul_one]
  rw [← Finset.prod_range_reflect]
  have h2 : ∀ i ∈ Finset.range (k : ℕ),
      (if (k : ℕ) - 1 - i < (k : ℕ) then (((k : ℕ) : ℝ) - (((k : ℕ) - 1 - i : ℕ) : ℝ)) else 1) =
        ((i + 1 : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]
    rw [Nat.cast_sub (by omega : i ≤ (k : ℕ) - 1), Nat.cast_sub (by omega : 1 ≤ (k : ℕ))]
    push_cast
    ring
  rw [Finset.prod_congr rfl h2, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
end Formalism.DegreeFormula.PFlagDeg
