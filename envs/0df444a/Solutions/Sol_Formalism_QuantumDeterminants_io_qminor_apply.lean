-- Prove2me | solution 1 for Formalism.QuantumDeterminants.io_qminor_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:49.092741+00:00
-- url     : https://prove2.me/submissions/e50829da-d500-4770-b1d9-0d2cfcc4de16

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
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (x : ioS ε E) :
    qminor (ioE ε E) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (ioE ε E) p.1 p.2.1 p.2.2).prod x := by
  simp only [qminor, LinearMap.sum_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Int.cast_smul_eq_zsmul, List.map_ofFn, Function.comp_def]
end Formalism.QuantumDeterminants
