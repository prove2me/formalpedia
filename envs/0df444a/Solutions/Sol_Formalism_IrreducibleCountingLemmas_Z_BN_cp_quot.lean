-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.cp_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:33.965904+00:00
-- url     : https://prove2.me/submissions/cd383640-9971-4701-a538-974a8e22fbcb

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_charpoly_eq_restrict_mul_mapQ

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
theorem _root_.solution {k A : Type} [Field k] [Ring A] [Algebra k A] {V : Type} [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V]
    (N : Submodule A V) (a : A) :
    cp k V a = cp k N a * cp k (V ⧸ N) a := by
  have he : N.restrictScalars k ≤ (N.restrictScalars k).comap (Algebra.lsmul k k V a) :=
    fun x hx => N.smul_mem a hx
  unfold cp
  rw [charpoly_eq_restrict_mul_mapQ (N.restrictScalars k) _ he]
  rfl
end Formalism.IrreducibleCountingLemmas.Z.BN
