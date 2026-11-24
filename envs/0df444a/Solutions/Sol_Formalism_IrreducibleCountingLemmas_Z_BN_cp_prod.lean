-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.cp_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:49.84404+00:00
-- url     : https://prove2.me/submissions/ece1aa48-268b-4425-b7db-c6d99f08e00b

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg

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
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W S : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup S] [Module A S]
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    cp k (V × W) a = cp k V a * cp k W a := by
  unfold cp
  rw [← LinearMap.charpoly_prodMap]
  congr 1
end Formalism.IrreducibleCountingLemmas.Z.BN
