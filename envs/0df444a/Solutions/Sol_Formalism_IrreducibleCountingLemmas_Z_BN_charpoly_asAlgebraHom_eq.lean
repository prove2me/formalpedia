-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_asAlgebraHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:52:59.591474+00:00
-- url     : https://prove2.me/submissions/ca213730-b335-4eed-9ec2-32ee0cd9df22

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_charpoly_asAlgebraHom_eq_alt

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
theorem _root_.solution [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W)
    (h : ∀ g, (ρ g).charpoly = (τ g).charpoly) (x : MonoidAlgebra k G) :
    (ρ.asAlgebraHom x).charpoly = (τ.asAlgebraHom x).charpoly :=
  charpoly_asAlgebraHom_eq_alt (AlgebraicClosure k) ρ τ h x
end Formalism.IrreducibleCountingLemmas.Z.BN
