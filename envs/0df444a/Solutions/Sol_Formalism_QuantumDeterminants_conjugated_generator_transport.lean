-- Prove2me | solution 1 for Formalism.QuantumDeterminants.conjugated_generator_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:26:09.35391+00:00
-- url     : https://prove2.me/submissions/64937e7f-18ef-460b-b8ce-ea5d16f8096d

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_eq
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUJ
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_single
import Theorems.Thm_Formalism_REAL_ecSumV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution : EabHTransport := by
  intro n ε E _ _ H P Q f a b g hQP hPQ hH hsm hg
  rw [ioh_EabH_eq ε H P Q f a b hQP hPQ hH g,
    ecSumV n ε E _ _ _ hsm (ioh_inUJ ε H P Q g hPQ hH hg)]
  simp only [ioh_single]
end Formalism.QuantumDeterminants
