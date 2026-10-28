-- Prove2me | solution 1 for ContextFooling.FoolingEq.cost_efficient_qualities
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:30:17.717378+00:00
-- url     : https://prove2.me/submissions/2de75c17-65e2-42ab-8c9a-edb760abf631

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

open ContextFooling.FoolingEq in
theorem solution (P : Params) (hP : P.Standing) :
    P.qS < P.qQ ∧ P.qP < P.qS ∧ 0 < P.qP := by
  obtain ⟨hβ, _, _, _, hc, _, h0, _, hcc, hqS, hS', hqQ, hQ', hqP, hP', _⟩ := hP
  have hcont : Continuous (deriv P.c) := hc.continuous_deriv (by norm_num)
  have hmono : StrictMonoOn (deriv P.c) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn
    intro x hx
    exact hcc x (interior_subset hx)
  have hβpos : 0 < P.β := by linarith
  refine ⟨?_, ?_, ?_⟩
  · apply (hmono.lt_iff_lt (Set.mem_Ici.mpr hqS) (Set.mem_Ici.mpr hqQ)).mp
    rw [hS', hQ']
    exact hβ
  · apply (hmono.lt_iff_lt (Set.mem_Ici.mpr hqP) (Set.mem_Ici.mpr hqS)).mp
    rw [hP', hS']
    exact (div_lt_one hβpos).mpr hβ
  · apply (hmono.lt_iff_lt (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hqP)).mp
    rw [h0, hP']
    positivity
