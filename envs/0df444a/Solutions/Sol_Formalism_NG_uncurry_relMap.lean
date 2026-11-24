-- Prove2me | solution 1 for Formalism.NG.uncurry_relMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:42.359799+00:00
-- url     : https://prove2.me/submissions/8f11c8a8-0c3b-4a38-aad4-9e63eee3aaea

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {g d : Type} [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O)
variable [SMulCommClass R O (LatQ O d ρ)]
namespace Formalism.NG
theorem _root_.solution (Θ : Matrix g g R) (v : g → LatQ O d ρ) :
    uncurryEquiv ρ (relMap O (LatQ O d ρ) Θ v) = matQ O (bigMat ρ Θ) (uncurryEquiv ρ v) := by
  funext p
  obtain ⟨i, a⟩ := p
  show (∑ j, Θ i j • v j : LatQ O d ρ) a = ∑ q : g × d, ρ (Θ i q.1) a q.2 • v q.1 q.2
  rw [Fintype.sum_prod_type]
  have hsum : (∑ j, Θ i j • v j : LatQ O d ρ) a = ∑ j, ((Θ i j • v j : LatQ O d ρ) : d → KO O) a :=
    Finset.sum_apply (M := fun _ : d => KO O) a univ (fun j => (Θ i j • v j : LatQ O d ρ))
  rw [hsum]
  rfl
end Formalism.NG
