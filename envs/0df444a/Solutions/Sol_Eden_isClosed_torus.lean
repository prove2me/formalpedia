-- Prove2me | solution 1 for Eden.isClosed_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:36.646287+00:00
-- url     : https://prove2.me/submissions/1e2f488b-6da0-412e-8d66-a8374aae4e26

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
import Theorems.Thm_P2M_Eden_continuous_radiusSq__4ecf54230f51
import Theorems.Thm_P2M_Eden_continuous_radiusSq__7af63be7ebdc

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution : IsClosed torus := by
  have hw : Continuous (fun p : PhaseSpace => p 4) := by fun_prop
  exact (isClosed_eq continuous_radiusSq₁ continuous_const).inter
    ((isClosed_eq continuous_radiusSq₂ continuous_const).inter
      (isClosed_eq hw continuous_const))
end Eden
