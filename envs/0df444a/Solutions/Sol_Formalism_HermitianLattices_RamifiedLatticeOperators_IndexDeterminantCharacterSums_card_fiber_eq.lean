-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.card_fiber_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:22.323903+00:00
-- url     : https://prove2.me/submissions/022aca1f-5cd8-4335-a8e3-5fc49ae0292a

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
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) (x0 : V) :
    Nat.card {x : V // L x = L x0} = Nat.card {x : V // L x = 0} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1 - x0, by rw [map_sub, x.2, sub_self]⟩
      invFun := fun y => ⟨y.1 + x0, by rw [map_add, y.2, zero_add]⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
