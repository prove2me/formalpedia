-- Prove2me | solution 1 for CohnElkies.manuscriptQuotientRootInf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/3857cbe6-d58e-4a22-a680-43f3ce14ee27

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_quotient_pos
import Theorems.Thm_CohnElkies_quotientSet_bddBelow
import Theorems.Thm_CohnElkies_admissible_nonempty
import Theorems.Thm_CohnElkies_manuscriptQuotientRootSet_eq_image

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution (d : ℕ) :
    sInf (manuscriptQuotientRootSet d) =
      (sInf (quotientSet d)) ^ ((d : ℝ)⁻¹) := by
  have hcontinuous :
      Continuous (fun x : ℝ => x ^ ((d : ℝ)⁻¹)) :=
    Real.continuous_rpow_const (by positivity)
  have hmono :
      MonotoneOn (fun x : ℝ => x ^ ((d : ℝ)⁻¹)) (quotientSet d) := by
    intro x hx y _ hxy
    obtain ⟨f, rfl⟩ := hx
    exact Real.rpow_le_rpow (quotient_pos f).le hxy (by positivity)
  obtain ⟨f⟩ := admissible_nonempty d
  have hnonempty : (quotientSet d).Nonempty :=
    ⟨quotient f, ⟨f, rfl⟩⟩
  rw [manuscriptQuotientRootSet_eq_image]
  exact
    (MonotoneOn.map_csInf_of_continuousWithinAt
      hcontinuous.continuousWithinAt hmono hnonempty
      (quotientSet_bddBelow d)).symm
end CohnElkies
