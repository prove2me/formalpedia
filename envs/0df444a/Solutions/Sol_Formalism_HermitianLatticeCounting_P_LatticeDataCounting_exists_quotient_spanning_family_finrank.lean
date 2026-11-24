-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.exists_quotient_spanning_family_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:13.556889+00:00
-- url     : https://prove2.me/submissions/2574fb55-4f0c-4d08-8ce7-3520daa1bdc5

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_gen_of_local
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_gen_mod_max

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
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (I : Ideal R) [Finite (M ⧸ (I • (⊤ : Submodule R M)))] :
    ∃ s : Fin (Module.finrank R M) → M ⧸ (I • (⊤ : Submodule R M)),
      Submodule.span R (Set.range s) = ⊤ := by
  apply gen_of_local
  intro P hP
  obtain ⟨s, hs⟩ := gen_mod_max (M := M) P
  refine ⟨(I • (⊤ : Submodule R M)).mkQ ∘ s, ?_⟩
  have h1 : (Submodule.span R (Set.range s) ⊔ P • (⊤ : Submodule R M)).map
      (I • (⊤ : Submodule R M)).mkQ = ⊤ := by
    rw [hs, Submodule.map_top, Submodule.range_mkQ]
  rw [Submodule.map_sup, Submodule.map_span, ← Set.range_comp, Submodule.map_smul'', Submodule.map_top,
    Submodule.range_mkQ] at h1
  exact h1
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
