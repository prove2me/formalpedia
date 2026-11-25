-- Prove2me | solution 1 for Formalism.NG.IdempotentImageSmul.fwd_bwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:53.963441+00:00
-- url     : https://prove2.me/submissions/068919fe-f983-4ce5-84db-2113ce74ea0b

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Theorems.Thm_Formalism_NG_IdempotentImageSmul_eps_smul_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentImageSmul
variable {O OO M Q : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M] [Module OO M]
    [Module O M] [IsScalarTower O OO M] [AddCommGroup Q] [Module O Q] (ε : OO)
variable {ε}
variable (ε) [SMulCommClass OO O (EpsDual O OO Q ε)]
variable {ε}
namespace Formalism.NG.IdempotentImageSmul
theorem _root_.solution (hε : IsIdempotentElem ε) (ψ : epsImg O (M := M) ε →ₗ[O] Q) :
    fwd ε (bwd ε ψ) = ψ := by
  apply LinearMap.ext
  intro y
  show ψ ⟨ε • y.1, _⟩ = ψ y
  congr 1
  apply Subtype.ext
  exact eps_smul_of_mem hε y
end Formalism.NG.IdempotentImageSmul
