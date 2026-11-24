-- Prove2me | solution 1 for Formalism.L2.PT.coe_glEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:45.270934+00:00
-- url     : https://prove2.me/submissions/f20403e4-b7b5-49b6-a8ce-5a041675440e

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
theorem _root_.solution (e : ι ≃ κ) (γ : GL κ K) :
    (((glEquiv K e).symm γ : GL ι K) : Matrix ι ι K) = Matrix.reindex e.symm e.symm (γ : Matrix κ κ K) := rfl
end Formalism.L2.PT
