-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.eq_zero_of_mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:54.088327+00:00
-- url     : https://prove2.me/submissions/b1e6fce5-5696-4ee3-8456-e9c64c9ae1cb

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
open ComplexOrder
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution {T : Submodule ℂ (ι → ℂ)} {y : ι → ℂ} (h1 : y ∈ T) (h2 : y ∈ perp T) : y = 0 :=
  dotProduct_star_self_eq_zero.1 (h2 y h1)
end CompanionTheory.D.gk.admitted
