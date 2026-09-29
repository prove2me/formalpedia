-- Prove2me | solution 1 for FamousTheorems.tietze_extension
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:15:55.82678+00:00
-- url     : https://prove2.me/submissions/3b97438f-c902-4768-87c2-75fe7ed063ed

import Mathlib

theorem solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace Y]
    (f : BoundedContinuousFunction X ℝ) {e : X → Y} (he : Topology.IsClosedEmbedding e) :
    ∃ g : BoundedContinuousFunction Y ℝ, ‖g‖ = ‖f‖ ∧ ⇑g ∘ e = ⇑f :=
  BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding f he
