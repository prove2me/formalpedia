-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_smul_top_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:47.232668+00:00
-- url     : https://prove2.me/submissions/07eb9534-7355-4ac2-985a-df629463e4ca

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
open NumberField Formalism.SLP.P.CountO
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (I : Ideal R) :
    I • (⊤ : Submodule R (M × N)) =
      (I • (⊤ : Submodule R M)).prod (I • (⊤ : Submodule R N)) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr m _
    exact ⟨Submodule.smul_mem_smul hr trivial, Submodule.smul_mem_smul hr trivial⟩
  · rintro ⟨m, n⟩ ⟨hm, hn⟩
    have e : ((m, n) : M × N) = LinearMap.inl R M N m + LinearMap.inr R M N n := by simp
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · have : LinearMap.inl R M N m ∈ (I • (⊤ : Submodule R M)).map (LinearMap.inl R M N) :=
        Submodule.mem_map_of_mem hm
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    · have : LinearMap.inr R M N n ∈ (I • (⊤ : Submodule R N)).map (LinearMap.inr R M N) :=
        Submodule.mem_map_of_mem hn
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
end Formalism.HermitianLatticeCounting.P
