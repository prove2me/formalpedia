-- Prove2me | solution 1 for Formalism.GrowthSums.le_padicValRat_sum_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:05.78266+00:00
-- url     : https://prove2.me/submissions/15c644b2-c6f5-4f09-bcfd-ff7cc426fe94

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Harmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
namespace Formalism.GrowthSums
theorem _root_.solution {p : ℕ} [Fact p.Prime] (s : ℤ) {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hpos : ∀ i ∈ S, 0 < F i) (hv : ∀ i ∈ S, s ≤ padicValRat p (F i)) :
    s ≤ padicValRat p (∑ i ∈ S, F i) := by
  revert hpos hv
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro _ hv
    simpa using hv a (Finset.mem_singleton_self a)
  | cons a T haT hT ih =>
    intro hpos hv
    have h1 : s ≤ padicValRat p (F a) := hv a (Finset.mem_cons.2 (Or.inl rfl))
    have h2 : s ≤ padicValRat p (∑ i ∈ T, F i) :=
      ih (fun i hi => hpos i (Finset.mem_cons.2 (Or.inr hi)))
        (fun i hi => hv i (Finset.mem_cons.2 (Or.inr hi)))
    have hpa : 0 < F a := hpos a (Finset.mem_cons.2 (Or.inl rfl))
    have hpT : 0 < ∑ i ∈ T, F i :=
      Finset.sum_pos (fun i hi => hpos i (Finset.mem_cons.2 (Or.inr hi))) hT
    have hne : F a + ∑ i ∈ T, F i ≠ 0 := (add_pos hpa hpT).ne'
    rw [Finset.sum_cons]
    exact le_trans (le_min h1 h2) (padicValRat.min_le_padicValRat_add hne)
end Formalism.GrowthSums
