-- Prove2me | solution 1 for Formalism.QuantumDeterminants.io_rep_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:27.973471+00:00
-- url     : https://prove2.me/submissions/3e480986-7fed-41fe-9275-e10d489f378b

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
theorem _root_.solution {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Matrix (Fin n) (Fin n) ℂ → E}
    {x : ι → ioS ε E} (h : ∀ i, IORep (F i) (x i).1) :
    IORep (fun g => ∑ i, c i • F i g) (∑ i, c i • x i).1 := by
  intro g hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i g hg]
end Formalism.QuantumDeterminants
