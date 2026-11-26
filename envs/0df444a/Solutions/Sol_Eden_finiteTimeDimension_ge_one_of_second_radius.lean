-- Prove2me | solution 1 for Eden.finiteTimeDimension_ge_one_of_second_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:06.278364+00:00
-- url     : https://prove2.me/submissions/5268d4ec-67f1-4301-8d71-1a4d127906ce

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_NeutralDimensionBounds
import Theorems.Thm_Eden_finiteTimeDimension_ge_one_of_tangential_factor
import Theorems.Thm_Eden_log_planarAmplitude_nonneg


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (hs : 1 ≤ radiusSq₂ p) :
    1 ≤ finiteTimeDimension c t p :=
  finiteTimeDimension_ge_one_of_tangential_factor c ht p 3
    (log_planarAmplitude_nonneg ht.le hs hp.2.1)
end Eden
