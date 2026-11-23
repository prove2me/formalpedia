-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.uw_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:52.07963+00:00
-- url     : https://prove2.me/submissions/b79d6f4d-6373-4462-8d10-80fde0120ec6

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_tau
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_row_of_fixed_col
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_fixed_col
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_out

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    block k r h := by
  have hU : h ∈ UH (Hpk k r) := by
    simp only [UWset, Set.mem_setOf_eq] at hh
    exact hh.1
  unfold block
  refine ⟨fun i j hj => uw_fixed_col hh j hj i, fun i j hi => ?_⟩
  have hc := uw_fixed_col hh (tau k r i) (tau_out i hi)
  have e := row_of_fixed_col hU (tau k r i) hc j
  rw [tau_tau] at e
  exact e
end Formalism.QuantumDeterminants.WeylGroupFacts
