-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.finrank_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:28.02086+00:00
-- url     : https://prove2.me/submissions/7cdaacab-649f-4f53-ab30-be8c8f0c5133

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution [FiniteDimensional E V] (B : Submodule (𝓞 E) V) :
    Module.finrank (𝓞 E) B ≤ Module.finrank E V := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := B) le_rfl
  have h1 : LinearIndependent (𝓞 E) (B.subtype ∘ f) := hf.map' B.subtype (Submodule.ker_subtype B)
  have h2 : LinearIndependent E (B.subtype ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 E) E).mp h1
  simpa using h2.fintype_card_le_finrank
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
