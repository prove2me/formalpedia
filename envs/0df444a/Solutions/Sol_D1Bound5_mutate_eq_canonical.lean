-- Prove2me | solution 1 for D1Bound5.mutate_eq_canonical
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:19.811004+00:00
-- url     : https://prove2.me/submissions/506da854-1d26-44ed-8c4d-076a17cd0108

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_rootCandidate_complete
import Theorems.Thm_D1Bound5_quadInt_mul_eq_zero

section
namespace D1Bound5
open QuadInt

















/-- Any actual root differs from the canonical one by sign, including zero. -/
theorem quadInt_root_eq_or_neg {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (z r : QuadInt tau nu) (hr : r*r = z) :
    r = rootCandidate z ∨ r = -rootCandidate z := by
  have hc := rootCandidate_complete hd ⟨r, hr⟩
  have hf : (r-rootCandidate z)*(r+rootCandidate z) = 0 := by
    linear_combination hr-hc
  rcases quadInt_mul_eq_zero hd hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)





/-- Arbitrary actual root choices give one of the two deterministic neighbors. -/
theorem _root_.solution {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (a b z r0 r s : QuadInt tau nu)
    (h0 : r0*r0 = a*b+1) (hr : r*r = a*z+1) (hs : s*s = b*z+1) :
    mutate a b z r0 r s = pairMutationPlus a b z ∨
    mutate a b z r0 r s = pairMutationMinus a b z := by
  rcases quadInt_root_eq_or_neg hd _ r0 h0 with h0 | h0 <;>
    rcases quadInt_root_eq_or_neg hd _ r hr with hr | hr <;>
    rcases quadInt_root_eq_or_neg hd _ s hs with hs | hs
  all_goals rw [h0, hr, hs]
  all_goals unfold pairMutationPlus pairMutationMinus mutate
  · left; ring
  · right; ring
  · right; ring
  · left; ring
  · right; ring
  · left; ring
  · left; ring
  · right; ring











end D1Bound5
end
