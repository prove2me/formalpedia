-- Prove2me | solution 1 for CohnElkies.eventually_linearProgram_pos_of_sharpQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/4ff7a122-9865-432a-a85f-604f320b9f6b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_geometricFactor_pos
import Theorems.Thm_CohnElkies_criticalRadius_pos
import Theorems.Thm_CohnElkies_normalizedProgram_eq_quotientInf_root_unconditional
import Theorems.Thm_CohnElkies_quotientInf_nonneg_unconditional

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (hquotient : SharpQuotientAsymptotic) :
    ∀ᶠ d : ℕ in atTop, 0 < linearProgram d := by
  have hnorm : ∀ᶠ d : ℕ in atTop, 0 < normalizedProgram d :=
    hquotient.eventually (Ioi_mem_nhds criticalRadius_pos)
  filter_upwards [hnorm, eventually_gt_atTop (0 : ℕ)] with d hpositive hd
  have hnonneg := quotientInf_nonneg_unconditional d
  have hinf : 0 < sInf (quotientSet d) := by
    by_contra hnot
    have hzero : sInf (quotientSet d) = 0 :=
      le_antisymm (le_of_not_gt hnot) hnonneg
    rw [normalizedProgram_eq_quotientInf_root_unconditional d,
      hzero] at hpositive
    have hdreal : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hd)
    simp [quotientRootMap, hdreal] at hpositive
  unfold linearProgram
  exact mul_pos (geometricFactor_pos d) hinf
end CohnElkies
