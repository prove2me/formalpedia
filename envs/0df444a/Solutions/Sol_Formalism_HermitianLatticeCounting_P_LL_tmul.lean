-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LL_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:18.060774+00:00
-- url     : https://prove2.me/submissions/9c463f54-3b44-4ec0-ad65-161e6da9e02d

import Definitions.Def_Formalism_FlagUnipotentLattices_InterlaceBlocksW
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] {n : ℕ}
    (ℓ : V →ₗ[ℂ] U) (a : Fin n) (v : V) (y : Fin n → ℂ) : LLmap ℓ a (v ⊗ₜ[ℂ] y) = y a • ℓ v := by
  simp [LLmap]
end Formalism.HermitianLatticeCounting.P
