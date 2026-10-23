-- Prove2me | solution 1 for CircletTSP.Facet.claim_3_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:06:04.435989+00:00
-- url     : https://prove2.me/submissions/4649543e-2fe6-4174-822e-8ff95f00f90f

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

set_option autoImplicit false

namespace CircletTSP.Facet.Base4

def unitEdges (π : Equiv.Perm (Fin 4)) : ℕ :=
  ∑ u : Fin 4, ∑ v : Fin 4,
    if u < v ∧ cycLen 4 u v = 1 then (MetricTSP.tourSteps π u v).card else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma two_le_unitEdges : ∀ π : Equiv.Perm (Fin 4), 2 ≤ unitEdges π := by
  decide

lemma form_eq (π : Equiv.Perm (Fin 4)) :
    circletForm 4 (MetricTSP.tourVec π) = (unitEdges π : ℝ) := by
  norm_num [circletForm, coeff, Finset.sum_Icc_succ_top]
  simp [lenCount, MetricTSP.tourVec, unitEdges]

end CircletTSP.Facet.Base4

open CircletTSP.Facet

theorem solution (π : Equiv.Perm (Fin 4)) :
    (4 : ℝ) - 2 ≤ circletForm 4 (MetricTSP.tourVec π) := by
  rw [Base4.form_eq]
  norm_num
  exact_mod_cast Base4.two_le_unitEdges π
