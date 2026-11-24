-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.card_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:32.09573+00:00
-- url     : https://prove2.me/submissions/252bd176-bd60-45d2-a168-b1bc69b44e91

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
variable {F : Type} [Field F] [Fintype F]
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module F V] [Fintype V] [AddCommGroup W]
    [Module F W] (L : V →ₗ[F] W) :
    Nat.card {x : V // L x = 0} = Fintype.card F ^ finrank F (LinearMap.ker L) := by
  classical
  rw [show Nat.card {x : V // L x = 0} = Nat.card (LinearMap.ker L) from
    Nat.card_congr (Equiv.subtypeEquivRight fun x => LinearMap.mem_ker.symm)]
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F)]
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
