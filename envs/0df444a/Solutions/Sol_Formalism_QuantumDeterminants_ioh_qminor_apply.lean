-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_qminor_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:00.18777+00:00
-- url     : https://prove2.me/submissions/6352f0e3-a035-41e1-acac-2b1cadb800d8

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated

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
theorem _root_.solution {t : ℕ} (Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E))
    (a b : Fin t → Fin n) (u : ℂ) (x : ioS ε E) :
    qminor Ealg a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm Ealg p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.intCast_apply, List.map_ofFn, Int.cast_smul_eq_zsmul]
  rfl
end Formalism.QuantumDeterminants
