-- Prove2me | solution 1 for CohnElkies.linearProgram_root_eq_geometric_mul_normalizedProgram_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/4cf1c335-0372-48a0-8619-9c6147ccbb0a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_linearProgram_root_eq_geometric_mul_normalizedProgram
import Theorems.Thm_CohnElkies_admissible_nonempty

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
    {d : ℕ} (hd : 0 < d) :
    (linearProgram d) ^ ((d : ℝ)⁻¹) =
      packingGeometricRoot d * normalizedProgram d :=
  linearProgram_root_eq_geometric_mul_normalizedProgram hd
    (admissible_nonempty d)
end CohnElkies
