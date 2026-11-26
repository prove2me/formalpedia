-- Prove2me | solution 1 for Eden.continuousOn_volumeDefect_integrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:13:12.990736+00:00
-- url     : https://prove2.me/submissions/88bbc700-f245-4a0f-b24a-0508a2350168

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
import Theorems.Thm_Eden_continuousOn_evolution
import Theorems.Thm_P2M_Eden_continuous_radiusSq__4ecf54230f51
import Theorems.Thm_P2M_Eden_continuous_radiusSq__7af63be7ebdc


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    ContinuousOn (fun τ => (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2) (Set.Ici 0) :=
  (((continuous_radiusSq₁.comp_continuousOn (continuousOn_evolution c p)).sub
    continuousOn_const).pow 2).add
    (((continuous_radiusSq₂.comp_continuousOn (continuousOn_evolution c p)).sub
      continuousOn_const).pow 2)
end Eden
