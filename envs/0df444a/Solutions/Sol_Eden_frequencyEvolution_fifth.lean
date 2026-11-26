-- Prove2me | solution 1 for Eden.frequencyEvolution_fifth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:15.78642+00:00
-- url     : https://prove2.me/submissions/e51bc936-7edb-426c-bc0c-da8ba1e1ce0c

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_FrequencyEvolution

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c ν t : ℝ) (p : PhaseSpace) :
    frequencyEvolution c ν t p 4 = Real.exp (-c * t) * p 4 := rfl
end Eden
