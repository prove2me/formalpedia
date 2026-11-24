-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioT_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:03.006826+00:00
-- url     : https://prove2.me/submissions/e2cd671e-d2c2-4779-838d-e872b8d3d408

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
theorem _root_.solution {F : Matrix (Fin n) (Fin n) ℂ → E} {φ : IOPt ε → E} (h : IORep F φ) (a b : Fin n) :
    IORep (EabV ε a b F) (ioT ε a b φ) := by
  intro g hg
  exact io_eab_congr (fun g' hg' => (h g' hg').trans (ioExt_at hg').symm) a b hg
end Formalism.QuantumDeterminants
