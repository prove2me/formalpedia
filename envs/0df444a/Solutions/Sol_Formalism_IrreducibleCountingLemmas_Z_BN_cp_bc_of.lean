-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.cp_bc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:49.082475+00:00
-- url     : https://prove2.me/submissions/bad59ffd-358f-4490-baad-48c43f5bc75d

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_asModule

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
theorem _root_.solution [FiniteDimensional k V] (K : Type) [Field K] [Algebra k K]
    (ρ : Representation k G V) (g : G) :
    cp K (bc K ρ).asModule (MonoidAlgebra.of K G g) = (ρ g).charpoly.map (algebraMap k K) := by
  rw [cp_asModule, Representation.asAlgebraHom_of, ← LinearMap.charpoly_baseChange]
  rfl
end Formalism.IrreducibleCountingLemmas.Z.BN
