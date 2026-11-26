-- Prove2me | solution 1 for EdenVerified.s09_recurrent_aperiodic_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:50.354837+00:00
-- url     : https://prove2.me/submissions/acfd9a82-9ac6-4172-80cc-7c66303c39f9

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_torusEvolution_no_positive_return
import Theorems.Thm_Eden_torus_recurrence_nhds


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (p : torus) :
    (∀ U : Set torus, U ∈ 𝓝 p → ∀ R : ℝ, 0 < R →
      ∃ t : ℝ, R < t ∧ torusEvolution c t p ∈ U) ∧
    (∀ t : ℝ, 0 < t → torusEvolution c t p ≠ p) :=
  ⟨fun U hU R hR => torus_recurrence_nhds c p hU hR,
    fun t ht => torusEvolution_no_positive_return c p ht⟩
end EdenVerified
