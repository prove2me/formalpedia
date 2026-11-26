-- Prove2me | solution 1 for Eden.singularValueFunction_integer_evolution_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:48:18.840189+00:00
-- url     : https://prove2.me/submissions/4a3aaad3-59af-4a1d-a970-558b771d92b6

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle
import Theorems.Thm_Eden_exteriorFactor_pos
import Theorems.Thm_Eden_isGreatest_exteriorFactor


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    0 < singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k := by
  obtain ⟨s, hs⟩ := (isGreatest_exteriorFactor hk c ht p).1
  rw [← hs]
  exact exteriorFactor_pos k c ht p s
end Eden
