-- Prove2me | solution 1 for Eden.finiteTimeDimension_ge_one_of_first_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:00.650527+00:00
-- url     : https://prove2.me/submissions/8708f5ec-267e-4c4d-8f73-4accfba20f1f

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
    {p : PhaseSpace} (hp : p ∈ attractor) (hs : 1 ≤ radiusSq₁ p) :
    1 ≤ finiteTimeDimension c t p :=
  finiteTimeDimension_ge_one_of_tangential_factor c ht p 1
    (log_planarAmplitude_nonneg ht.le hs hp.1)
end Eden
