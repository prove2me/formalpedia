-- Prove2me | solution 1 for CircuitLowerBound.TabF.G_polyT
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:27:51.931452+00:00
-- url     : https://prove2.me/submissions/a03a9470-554e-42dc-9818-050e62b9ca98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CircuitLowerBound_TabF_clipE_polyT
import Theorems.Thm_CircuitLowerBound_TabF_clauseAt_polyT
import Theorems.Thm_CircuitLowerBound_TabF_kb_clipE_unary
import Theorems.Thm_CircuitLowerBound_TabF_lam_clipE_unary
import Theorems.Thm_CircuitLowerBound_TabF_nb_unary
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_unary_min_length
import Theorems.Thm_Groundwork_Unary_of_length

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]

attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.range
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.pow_unary
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] CircuitLowerBound.TabF.clipE_polyT

theorem solution : PolyT G := by
  unfold G
  apply Groundwork.PolyT.map
  · apply CircuitLowerBound.TabF.clauseAt_polyT
    · fun_prop
    · exact CircuitLowerBound.TabF.kb_clipE_unary (by fun_prop)
        (Groundwork.Unary.of_length (by fun_prop))
    · exact CircuitLowerBound.TabF.lam_clipE_unary (by fun_prop)
        (Groundwork.Unary.of_length (by fun_prop))
    · exact Groundwork.Unary.of_length (by fun_prop)
    · fun_prop
    · fun_prop
  · apply Groundwork.PolyT.range
    apply Groundwork.PolyT.unary_min_length
    · apply Groundwork.PolyT.pow_unary
      · fun_prop
      · exact CircuitLowerBound.TabF.nb_unary (by fun_prop)
          (CircuitLowerBound.TabF.lam_clipE_unary (by fun_prop)
            (Groundwork.Unary.of_length (by fun_prop)))
          (Groundwork.Unary.of_length (by fun_prop))
    · fun_prop
