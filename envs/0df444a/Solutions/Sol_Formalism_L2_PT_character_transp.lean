-- Prove2me | solution 1 for Formalism.L2.PT.character_transp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:11:09.780671+00:00
-- url     : https://prove2.me/submissions/a05232db-de7c-4a74-bbeb-ce2b75c89ad6

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.PT
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace Formalism.L2.PT
theorem _root_.solution (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (γ : GL κ K) :
    (transp e τ).character γ = τ.character ((glEquiv K e).symm γ) := rfl
end Formalism.L2.PT
