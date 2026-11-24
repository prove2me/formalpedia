-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_swap_blocks_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:38.595645+00:00
-- url     : https://prove2.me/submissions/e445dd9c-0b5a-4841-a6ef-8ba9417518b6

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Matrix Polynomial
variable {R : Type} [CommRing R]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] :
    (fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R)).det =
      (-1) ^ Fintype.card n := by
  have h : (fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R)) =
      fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg]
end Formalism.HermitianLatticeCounting.P
