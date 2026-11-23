-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:53.16042+00:00
-- url     : https://prove2.me/submissions/abcc6ba2-109a-4acb-91f9-bc6b99504a40

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_mul_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_tau
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_sgn_tau
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_sgn_mul_self

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
theorem _root_.solution : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, sgn_mul_self]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
end Formalism.QuantumDeterminants.WeylGroupFacts
