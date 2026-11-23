-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.isInt_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:57.85314+00:00
-- url     : https://prove2.me/submissions/f14baebe-2571-4aff-b636-3bcd218efeb6

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
theorem _root_.solution (σ : E →+* E) {a : E} (ha : IsInt a) : IsInt (σ a) := by
  obtain ⟨x, rfl⟩ := ha
  first
  | exact ⟨⟨σ x, (NumberField.RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom⟩, rfl⟩
  | exact ⟨⟨σ x, x.2.map σ.toIntAlgHom⟩, rfl⟩
  | exact ⟨NumberField.RingOfIntegers.mapRingHom σ x, rfl⟩
end Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
