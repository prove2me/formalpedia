-- Prove2me | solution 1 for Eden.singularValueFunction_evolution_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:01.002807+00:00
-- url     : https://prove2.me/submissions/70e54035-001a-46cf-802d-f76fb566337f

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle
import Theorems.Thm_Eden_singularValueFunction_integer_comp_le
import Theorems.Thm_Eden_fderiv_evolution_add

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) (c : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (p : PhaseSpace) :
    singularValueFunction (fderiv ℝ (evolution c (s + t)) p).toLinearMap k ≤
      singularValueFunction (fderiv ℝ (evolution c t) (evolution c s p)).toLinearMap k *
        singularValueFunction (fderiv ℝ (evolution c s) p).toLinearMap k := by
  rw [fderiv_evolution_add c hs ht p]
  exact singularValueFunction_integer_comp_le hk _ _
end Eden
