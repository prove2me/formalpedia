-- Prove2me | solution 1 for CohnElkies.normalizedProgram_eq_quotientInf_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/56027a4b-65c9-430e-aadd-ed1f69146dab

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_quotientSet_bddBelow
import Theorems.Thm_CohnElkies_continuous_quotientRootMap
import Theorems.Thm_CohnElkies_monotoneOn_quotientRootMap
import Theorems.Thm_CohnElkies_normalizedCostRange_eq_quotientRootImage

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Set
namespace CohnElkies
theorem _root_.solution
    (d : ℕ) (hadmissible : Nonempty (Admissible d)) :
    normalizedProgram d =
      quotientRootMap d (sInf (quotientSet d)) := by
  obtain ⟨f⟩ := hadmissible
  have hnonempty : (quotientSet d).Nonempty :=
    ⟨quotient f, ⟨f, rfl⟩⟩
  unfold normalizedProgram
  rw [normalizedCostRange_eq_quotientRootImage]
  exact
    (MonotoneOn.map_csInf_of_continuousWithinAt
      (continuous_quotientRootMap d).continuousWithinAt
      (monotoneOn_quotientRootMap d) hnonempty
      (quotientSet_bddBelow d)).symm
end CohnElkies
