-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:52:36.950259+00:00
-- url     : https://prove2.me/submissions/87ccfd5e-8aa0-4557-a9ec-98506112b5d4

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
import Theorems.Thm_Eden_squaredRadiusEvolution_le_two_iff
import Theorems.Thm_Eden_squaredRadiusEvolution_le_initial

set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) :
    squaredRadiusEvolution t s ≤ max s 2 := by
  rcases le_total s 2 with hs | hs
  · exact le_trans ((squaredRadiusEvolution_le_two_iff ht).2 hs) (le_max_right _ _)
  · exact le_trans (squaredRadiusEvolution_le_initial ht hs) (le_max_left _ _)
end Eden
