-- Prove2me | solution 1 for FairSelling.kept_eq_of_money_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:52.533957+00:00
-- url     : https://prove2.me/submissions/c9439ba2-ea75-4425-a45b-dbff236fddf0

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSSefx
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (j : Fin n) (hmoney : (unifiedOutcome v p A F q).money j = 0) :
    (unifiedOutcome v p A F q).kept j = A j ∧ q j = 0 := by
  classical
  simp only [unifiedOutcome] at hmoney ⊢
  have hsum : ∑ g ∈ (A j).filter (fun g => v j g < p g), p g = 0 := by
    have h0 : 0 ≤ ∑ g ∈ (A j).filter (fun g => v j g < p g), p g :=
      Finset.sum_nonneg (fun g _ => hp g)
    linarith [hq j]
  have hqj : q j = 0 := by linarith [Finset.sum_nonneg (fun g (_ : g ∈ (A j).filter
    (fun g => v j g < p g)) => hp g)]
  refine ⟨?_, hqj⟩
  have hempty : (A j).filter (fun g => v j g < p g) = ∅ := by
    by_contra hne
    obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hgmem := hg
    simp only [Finset.mem_filter] at hgmem
    have hpos : 0 < p g := lt_of_le_of_lt (hv j g) hgmem.2
    have : p g ≤ ∑ x ∈ (A j).filter (fun g => v j g < p g), p x :=
      Finset.single_le_sum (fun x _ => hp x) hg
    linarith
  refine Finset.filter_true_of_mem (fun g hg => ?_)
  intro hlt
  have : g ∈ (A j).filter (fun g => v j g < p g) := Finset.mem_filter.mpr ⟨hg, hlt⟩
  rw [hempty] at this
  exact absurd this (Finset.notMem_empty g)
end FairSelling
