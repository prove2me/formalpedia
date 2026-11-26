-- Prove2me | solution 1 for Eden.normalizedLogSingularValues_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:28.99985+00:00
-- url     : https://prove2.me/submissions/3eae8b3d-5aee-414a-bb08-e8a8a0f241a6

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
import Theorems.Thm_Eden_singularValues_evolution_pos

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) : Antitone (normalizedLogSingularValues c t p) := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (singularValues_evolution_pos c ht.le p j)
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues_antitone hij)) ht.le
end Eden
