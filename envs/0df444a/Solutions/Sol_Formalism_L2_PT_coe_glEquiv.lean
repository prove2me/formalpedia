-- Prove2me | solution 1 for Formalism.L2.PT.coe_glEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:11:20.130811+00:00
-- url     : https://prove2.me/submissions/f8d0fc7b-098d-4b43-9122-c507d5eb8b40

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
theorem _root_.solution (e : ι ≃ κ) (u : GL ι K) :
    ((glEquiv K e u : GL κ K) : Matrix κ κ K) = Matrix.reindex e e (u : Matrix ι ι K) := rfl
end Formalism.L2.PT
