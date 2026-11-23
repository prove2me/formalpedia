-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.exists_elt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:43.78343+00:00
-- url     : https://prove2.me/submissions/33466dc3-e0cd-45ca-a5f6-dd94b6df2b32

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : ∃ g : UJ ε, toM g = m := by
  have : m ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hm
  exact this
end CompanionTheory.D.gk.admitted
