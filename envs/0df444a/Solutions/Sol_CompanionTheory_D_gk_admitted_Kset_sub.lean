-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Kset_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:25.441066+00:00
-- url     : https://prove2.me/submissions/4a3dd591-87be-4be3-bb0a-d384878985e8

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
theorem _root_.solution {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ Kset ε) : m ∈ UJset ε := by
  have h1 : mᴴ * m = 1 := Matrix.mem_unitaryGroup_iff'.1 hm.1
  show mᴴ * Jm ε * m = Jm ε
  rw [Matrix.mul_assoc, ← hm.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
end CompanionTheory.D.gk.admitted
