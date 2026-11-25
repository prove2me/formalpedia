-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.coord_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:26.671355+00:00
-- url     : https://prove2.me/submissions/659e02e5-ed4c-4b80-a62d-438b7076895f

import Definitions.Def_Formalism_FlagUnipotentLattices_InterlaceBlocksW
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LL_tmul

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ξ : Fin n → V) (a : Fin n) :
    LLmap LinearMap.id a (∑ c, ξ c ⊗ₜ[ℂ] (Pi.single c (1 : ℂ) : Fin n → ℂ)) = ξ a := by
  simp only [map_sum, LL_tmul, LinearMap.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
  · simp
end Formalism.HermitianLatticeCounting.P
