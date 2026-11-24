-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:28.026978+00:00
-- url     : https://prove2.me/submissions/9cd803c8-59c6-419c-8443-2d73cc9cf385

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_io_gl


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
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution (hAd : GlRelAd) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) :
    GlRel (iohE ε E P Q) :=
  hAd (Module.End ℂ (ioS ε E)) n (ioE ε E) P Q (io_gl ε E) hQP
end Formalism.QuantumDeterminants
