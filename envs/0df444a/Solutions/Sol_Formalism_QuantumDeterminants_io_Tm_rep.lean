-- Prove2me | solution 1 for Formalism.QuantumDeterminants.io_Tm_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:42:30.526258+00:00
-- url     : https://prove2.me/submissions/bceab971-7325-4476-9a25-4be53b24db87

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Theorems.Thm_Formalism_QuantumDeterminants_ioE_rep

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
theorem _root_.solution {F : Matrix (Fin n) (Fin n) ℂ → E} {x : ioS ε E} (h : IORep F x.1) (u : ℂ)
    (a b : Fin n) : IORep (Top (EabV ε) u a b F) (Tm (ioE ε E) u a b x).1 := by
  intro g hg
  simp only [Top, Tm]
  split_ifs with hab
  · simp only [LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add, Submodule.coe_smul,
      Pi.add_apply, Pi.smul_apply, h g hg, ioE_rep h a b g hg]
  · simp only [LinearMap.add_apply, LinearMap.zero_apply, zero_add, ioE_rep h a b g hg]
end Formalism.QuantumDeterminants
