-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.cp_asModule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:29.177008+00:00
-- url     : https://prove2.me/submissions/49c387f5-7e90-473c-9bda-364c1346e213

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt

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
open TensorProduct
variable {k G V W : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution [FiniteDimensional k V] (ρ : Representation k G V) (x : MonoidAlgebra k G) :
    cp k ρ.asModule x = (ρ.asAlgebraHom x).charpoly := by
  rw [cp, ← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
  congr 1
end Formalism.IrreducibleCountingLemmas.Z.BN
