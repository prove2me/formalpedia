-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.cp_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:16:30.694313+00:00
-- url     : https://prove2.me/submissions/00ffaa47-545d-42be-a9e8-b554cc4f62b9

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_charpoly_mem_closure_simple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {k A : Type} [Field k] [Ring A] [Algebra k A] (V : Type) [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V] :
    (cp k V : A → k[X]) ∈ Submonoid.closure (simpleCps k A) :=
  charpoly_mem_closure_simple _ V rfl
end Formalism.IrreducibleCountingLemmas.Z.BN
