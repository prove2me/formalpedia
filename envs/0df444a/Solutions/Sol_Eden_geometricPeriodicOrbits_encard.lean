-- Prove2me | solution 1 for Eden.geometricPeriodicOrbits_encard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:00.543155+00:00
-- url     : https://prove2.me/submissions/c5aa0730-601e-4936-89bc-e23bf4864692

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
import Definitions.Def_Eden_PeriodicOrbits
import Theorems.Thm_Eden_firstCircle_ne_firstCircle
import Theorems.Thm_Eden_secondCircle_ne_secondCircle
import Theorems.Thm_Eden_firstCircle_ne_secondCircle
import Theorems.Thm_Eden_geometricPeriodicOrbits_eq

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    (geometricPeriodicOrbits c).encard = 4 := by
  apply Set.encard_eq_four.mpr
  refine ⟨firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2, ?_, ?_, ?_, ?_, ?_, ?_,
    geometricPeriodicOrbits_eq hc⟩
  · exact firstCircle_ne_firstCircle (by norm_num) (by norm_num)
  · exact firstCircle_ne_secondCircle (by norm_num)
  · exact firstCircle_ne_secondCircle (by norm_num)
  · exact firstCircle_ne_secondCircle (by norm_num)
  · exact firstCircle_ne_secondCircle (by norm_num)
  · exact secondCircle_ne_secondCircle (by norm_num) (by norm_num)
end Eden
