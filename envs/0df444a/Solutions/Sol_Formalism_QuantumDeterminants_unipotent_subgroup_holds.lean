-- Prove2me | solution 1 for Formalism.QuantumDeterminants.unipotent_subgroup_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:28.312159+00:00
-- url     : https://prove2.me/submissions/b9dfb778-4d5c-4a31-8af3-f891d905f357

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_one
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv

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
open WeylGroupFacts
namespace Formalism.QuantumDeterminants
theorem _root_.solution : NSubgroup := by
  unfold NSubgroup
  exact fun k r => ⟨WeylGroupFacts.mem_n_one, fun g hg h hh => WeylGroupFacts.mem_n_mul hg hh,
    fun g hg => WeylGroupFacts.mem_n_inv hg⟩
end Formalism.QuantumDeterminants
