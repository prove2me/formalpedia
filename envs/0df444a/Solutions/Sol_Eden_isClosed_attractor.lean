-- Prove2me | solution 1 for Eden.isClosed_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:34.861014+00:00
-- url     : https://prove2.me/submissions/8ceb16e2-ab21-4ecf-8e6e-f8388d9b9980

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
theorem _root_.solution : IsClosed attractor := by
  have hw : Continuous (fun p : PhaseSpace => p 4) := by fun_prop
  exact (isClosed_le continuous_radiusSq₁ continuous_const).inter
    ((isClosed_le continuous_radiusSq₂ continuous_const).inter
      (isClosed_eq hw continuous_const))
end Eden
