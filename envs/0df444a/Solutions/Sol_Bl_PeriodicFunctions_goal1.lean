-- Prove2me | solution 1 for Bl.PeriodicFunctions.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:24.215785+00:00
-- url     : https://prove2.me/submissions/26909b08-bff1-40f5-8e3f-819e222fea85

import Mathlib
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Module
namespace Bl.PeriodicFunctions
variable {K : Type} [Field K]
private theorem periodic_apply_mul_add (M : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) (k x : ℕ) :
    g (M * k + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, show M * k + M + x = (M * k + x) + M by ring, hg, ih]
end Bl.PeriodicFunctions
end

set_option autoImplicit false
open NumberField IsDedekindDomain Module
open Bl Bl.PeriodicFunctions
variable {K : Type} [Field K]
namespace Bl.PeriodicFunctions
theorem _root_.solution (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [periodic_apply_mul_add M g hg n]
    push_cast
    ring
end Bl.PeriodicFunctions
