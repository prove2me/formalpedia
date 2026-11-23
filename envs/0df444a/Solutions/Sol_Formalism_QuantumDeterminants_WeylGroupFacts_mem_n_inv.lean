-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:26.793198+00:00
-- url     : https://prove2.me/submissions/a79a2054-6d0e-4b9c-b3ab-aa09da4ad221

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_of_left_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g⁻¹ ∈ Nset k r := by
  have hg' := (nset_iff g).1 hg
  have hd := isUnit_of_uh hg'.1
  exact (nset_iff _).2 ⟨uh_inv hg'.1, col_of_left_inv hg'.2 (Matrix.nonsing_inv_mul g hd)⟩
end Formalism.QuantumDeterminants.WeylGroupFacts
