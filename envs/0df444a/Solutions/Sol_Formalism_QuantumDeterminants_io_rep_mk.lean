-- Prove2me | solution 1 for Formalism.QuantumDeterminants.io_rep_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:33.594575+00:00
-- url     : https://prove2.me/submissions/e27d348b-f4f4-4a42-873f-f0a26e1967dd

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
theorem _root_.solution {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) :
    ∃ x : ioS ε E, IORep f x.1 := by
  refine ⟨⟨fun g => f g.1, ?_⟩, fun g hg => rfl⟩
  show SmoothOnGV ε (ioExt ε (fun g : IOPt ε => f g.1))
  exact io_smooth_congr (fun g hg => (ioExt_at (φ := fun g : IOPt ε => f g.1) hg).symm) hf
end Formalism.QuantumDeterminants
