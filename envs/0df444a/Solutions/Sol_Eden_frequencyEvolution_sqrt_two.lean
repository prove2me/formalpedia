-- Prove2me | solution 1 for Eden.frequencyEvolution_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:10.223984+00:00
-- url     : https://prove2.me/submissions/ec12b6ea-3d6e-4122-9b48-969c224dc706

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_FrequencyEvolution

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c t : ℝ) :
    frequencyEvolution c (Real.sqrt 2) t = evolution c t := rfl
end Eden
