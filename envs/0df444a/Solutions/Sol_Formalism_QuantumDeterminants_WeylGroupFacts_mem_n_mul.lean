-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:11.227376+00:00
-- url     : https://prove2.me/submissions/c7692002-1390-4148-b4b0-2d41f6b7ab4b

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul

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
theorem _root_.solution {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) : g * h ∈ Nset k r := by
  have hg' := (nset_iff g).1 hg
  have hh' := (nset_iff h).1 hh
  exact (nset_iff _).2 ⟨uh_mul hg'.1 hh'.1, col_mul hg'.2 hh'.2⟩
end Formalism.QuantumDeterminants.WeylGroupFacts
