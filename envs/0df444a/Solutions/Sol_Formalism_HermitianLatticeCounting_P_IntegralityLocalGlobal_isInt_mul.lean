-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.isInt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:52.586422+00:00
-- url     : https://prove2.me/submissions/19011369-fee3-4a16-b89e-d542f53a87b0

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
theorem _root_.solution {a b : E} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  first
  | exact ha.mul hb
  | exact IsIntegral.mul ha hb
  | (obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x * y, by rw [← hx, ← hy]; push_cast; ring⟩)
end Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
