-- Prove2me | solution 1 for FairSelling.epsSEFX_unifiedOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:02.431943+00:00
-- url     : https://prove2.me/submissions/fa886ca8-71cc-49ad-9802-ec15136e7baa

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSSefx
import Theorems.Thm_FairSelling_lhs_unifiedOutcome
import Theorems.Thm_FairSelling_rhs_unifiedOutcome_le
import Theorems.Thm_FairSelling_kept_eq_of_money_zero
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsafe : ∀ i j, CSafe v p eps A q i j) :
    epsSEFX v p eps (unifiedOutcome v p A F q) := by
  classical
  intro i j
  set o := unifiedOutcome v p A F q with ho
  have hlhs : vbarSum (v i) p (o.kept i) + o.money i = vbarSum (v i) p (A i) + q i :=
    lhs_unifiedOutcome v p A F q i
  constructor
  · -- the envied bundle carries money: the full envy-free condition is required
    intro hpos
    rcases hsafe i j with hEF | ⟨hqj, hkeep, _⟩
    · have := rhs_unifiedOutcome_le v p A F q i j
      rw [hlhs]
      linarith
    · -- if `j` keeps its whole bundle and holds no banked money it receives nothing
      exfalso
      have hmz : o.money j = 0 := by
        simp only [ho, unifiedOutcome]
        have hempty : (A j).filter (fun g => v j g < p g) = ∅ := by
          refine Finset.filter_false_of_mem (fun g hg => ?_)
          exact not_lt.mpr (hkeep g hg)
        rw [hempty, hqj]
        simp
      rw [hmz] at hpos
      exact lt_irrefl 0 hpos
  · -- the envied bundle carries no money
    intro hzero
    obtain ⟨hkept, hqj⟩ := kept_eq_of_money_zero v p hv hp A F q hq j hzero
    rcases hsafe i j with hEF | ⟨_, _, hX⟩
    · left
      rw [hlhs, hkept]
      rw [hqj] at hEF
      linarith
    · right
      intro g hg
      rw [hkept] at hg
      have := hX g hg
      rw [hlhs, hkept]
      linarith
end FairSelling
