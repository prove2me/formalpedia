-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_mem_perpR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:21.980292+00:00
-- url     : https://prove2.me/submissions/6529db22-6a4c-4d9a-b7c0-7dc6f0b34a51

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
    (B : V →ₗ[K] V →ₛₗ[σ] K) (A : Submodule K V) (x : V) :
    x ∈ perpR B A ↔ ∀ a ∈ A, B a x = 0 := by
  simp [perpR, Submodule.mem_iInf]
end Formalism.HermitianLatticeCounting.P
