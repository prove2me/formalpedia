-- Prove2me | solution 1 for ConnesRigidity.gamma_pairwise_nonisomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/d1192c74-0a3b-4944-ac1d-3167d85eb39c

import Mathlib
import Definitions.Def_ConnesRigidity
import Theorems.Thm_ConnesRigidity_gamma_parameter_eq_of_mulEquiv

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
noncomputable section
open ConnesRigidity
namespace ConnesRigidity
theorem _root_.solution {m n : ℕ} (hmn : m ≠ n) :
    ¬GroupsIsomorphic (gammaGroup m) (gammaGroup n) := by
  rintro ⟨f⟩
  exact hmn (gamma_parameter_eq_of_mulEquiv f)
end ConnesRigidity
