-- Prove2me | solution 1 for Eden.supremum_asymptoticDimension_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:28.646006+00:00
-- url     : https://prove2.me/submissions/406eeeca-e35d-4813-b9dd-dc6c733656f8

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_asymptoticDimension_attractor_isGreatest

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' attractor) = targetDimension c :=
  (asymptoticDimension_attractor_isGreatest hc).csSup_eq
end Eden
