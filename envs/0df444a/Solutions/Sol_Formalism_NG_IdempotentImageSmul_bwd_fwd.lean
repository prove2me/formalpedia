-- Prove2me | solution 1 for Formalism.NG.IdempotentImageSmul.bwd_fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:41.050644+00:00
-- url     : https://prove2.me/submissions/a8d58ab9-f150-40f3-bdaf-c93761a83189

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Theorems.Thm_Formalism_NG_IdempotentImageSmul_eps_mul_of_mem

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
theorem _root_.solution (hε : IsIdempotentElem ε) (Φ : M →ₗ[OO] EpsDual O OO Q ε) :
    bwd ε (fwd ε Φ) = Φ := by
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  show Φ (x.1 • m) (epsE ε) = Φ m x
  rw [Φ.map_smul, dual_smul_apply]
  congr 1
  apply Subtype.ext
  show ε * x.1 = x.1
  exact eps_mul_of_mem hε x
end Formalism.NG.IdempotentImageSmul
