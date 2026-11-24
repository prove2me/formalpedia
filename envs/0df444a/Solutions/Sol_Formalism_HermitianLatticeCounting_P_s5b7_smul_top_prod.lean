-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_smul_top_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:26.49182+00:00
-- url     : https://prove2.me/submissions/62ed037b-4eef-4930-834d-474490683858

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module
variable {O : Type} [CommRing O] [IsDedekindDomain O]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (I : Ideal R) :
    I • (⊤ : Submodule R (M × N)) =
      (I • (⊤ : Submodule R M)).prod (I • (⊤ : Submodule R N)) := by
  apply le_antisymm
  · intro x hx
    constructor
    · have : (I • (⊤ : Submodule R (M × N))).map (LinearMap.fst R M N) ≤ I • ⊤ := by
        rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
      exact this ⟨x, hx, rfl⟩
    · have : (I • (⊤ : Submodule R (M × N))).map (LinearMap.snd R M N) ≤ I • ⊤ := by
        rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
      exact this ⟨x, hx, rfl⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have h1 : (I • (⊤ : Submodule R M)).map (LinearMap.inl R M N) ≤ I • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    have h2 : (I • (⊤ : Submodule R N)).map (LinearMap.inr R M N) ≤ I • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    have e : ((a, b) : M × N) = LinearMap.inl R M N a + LinearMap.inr R M N b := by simp
    rw [e]
    exact Submodule.add_mem _ (h1 ⟨a, ha, rfl⟩) (h2 ⟨b, hb, rfl⟩)
end Formalism.HermitianLatticeCounting.P
