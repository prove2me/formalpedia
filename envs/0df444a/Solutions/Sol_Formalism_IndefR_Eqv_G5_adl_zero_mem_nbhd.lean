-- Prove2me | solution 1 for Formalism.IndefR.Eqv.G5.adl_zero_mem_nbhd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:07.626385+00:00
-- url     : https://prove2.me/submissions/1b6885fa-5a4c-4cce-b886-88c613a60529

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
open scoped AdeleRing
namespace Formalism.IndefR.Eqv.G5
theorem _root_.solution : (0 : AdeleRing (𝓞 F) F) ∈ adlNbhd F := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have h0 : (0 : AdeleRing (𝓞 F) F).1 w = 0 := rfl
    rw [h0, norm_zero]
    exact one_pos
  · first | exact zero_mem _ | simp
end Formalism.IndefR.Eqv.G5
