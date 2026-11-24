-- Prove2me | solution 1 for FairSelling.GeneralTPS.epsSEFXu_unifiedOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:10.852024+00:00
-- url     : https://prove2.me/submissions/4355ed90-9060-4c1f-8e88-831c30cfc7fc

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_lhs_unifiedOutcome
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_rhs_unifiedOutcome_le
import Theorems.Thm_FairSelling_vbarSum_sdiff_singleton
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ)
    (hsafe : ∀ i j, CSafeU v p eps A q i j) :
    epsSEFXu v p eps (unifiedOutcome v p A F q) := by
  classical
  intro i j
  set o := unifiedOutcome v p A F q with ho
  have hlhs : vbarSum (v i) p (o.kept i) + o.money i = vbarSum (v i) p (A i) + q i :=
    lhs_unifiedOutcome v p A F q i
  have hrhs : vbarSum (v i) p (o.kept j) + o.money j ≤ vbarSum (v i) p (A j) + q j :=
    rhs_unifiedOutcome_le v p A F q i j
  refine ⟨fun _ => ?_, fun g hg => ?_⟩
  · rcases hsafe i j with hEF | ⟨hqj, hkeep, _⟩
    · rw [hlhs]; linarith
    · -- an agent that keeps its whole bundle and banks nothing receives no money
      have hmz : o.money j = 0 := by
        simp only [ho, unifiedOutcome]
        have hempty : (A j).filter (fun g => v j g < p g) = ∅ :=
          Finset.filter_false_of_mem (fun g hg => not_lt.mpr (hkeep g hg))
        rw [hempty, hqj]; simp
      rw [hlhs, hmz]
      have : vbarSum (v i) p (o.kept j) ≤ vbarSum (v i) p (A j) + q j := by
        have := hrhs; rw [hmz] at this; linarith
      rw [hqj] at this
      linarith
  · -- the up-to-any-good clause
    have hsub : o.kept j ⊆ A j := by
      simp only [ho, unifiedOutcome]
      exact Finset.filter_subset _ _
    rcases hsafe i j with hEF | ⟨hqj, hkeep, hX⟩
    · have hsplit : vbarSum (v i) p (o.kept j)
          = vbarSum (v i) p (o.kept j \ {g}) + vbar (v i) p g :=
        vbarSum_sdiff_singleton hg
      have hpg : p g ≤ vbar (v i) p g := le_max_left _ _
      rw [hlhs]
      linarith
    · -- the owner keeps everything, so its kept bundle is its whole bundle
      have hkept : o.kept j = A j := by
        simp only [ho, unifiedOutcome]
        exact Finset.filter_true_of_mem (fun x hx => not_lt.mpr (hkeep x hx))
      have hmz : o.money j = 0 := by
        simp only [ho, unifiedOutcome]
        have hempty : (A j).filter (fun g => v j g < p g) = ∅ :=
          Finset.filter_false_of_mem (fun x hx => not_lt.mpr (hkeep x hx))
        rw [hempty, hqj]; simp
      rw [hlhs, hmz, hkept]
      rw [hkept] at hg
      have := hX g hg
      linarith
end FairSelling.GeneralTPS
