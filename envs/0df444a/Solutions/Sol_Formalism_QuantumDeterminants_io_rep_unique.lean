-- Prove2me | solution 1 for Formalism.QuantumDeterminants.io_rep_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:59:01.888135+00:00
-- url     : https://prove2.me/submissions/1ec87a17-31b4-4202-a6e6-843abe44e597

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral

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
theorem _root_.solution {F : Matrix (Fin n) (Fin n) ℂ → E} {x y : ioS ε E} (hx : IORep F x.1)
    (hy : IORep F y.1) : x = y := by
  apply Subtype.ext
  funext g
  exact (hx g.1 g.2).symm.trans (hy g.1 g.2)
end Formalism.QuantumDeterminants
