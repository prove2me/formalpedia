-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_Tm_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:05:14.397278+00:00
-- url     : https://prove2.me/submissions/c6a49672-bc81-48d3-9747-2ce7cf64bebc

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
theorem _root_.solution {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    {F : Matrix (Fin n) (Fin n) ℂ → E} {x : ioS ε E} (h : IORep F x.1) (u : ℂ)
    (a b : Fin n) : IORep (Top Eop u a b F) (Tm Ealg u a b x).1 := by
  intro g hg
  have he := hR a b F x h g hg
  unfold Top Tm
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, he, h g hg]
  · rw [if_neg hab, if_neg hab, zero_add, zero_add, he]
end Formalism.QuantumDeterminants
