-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.smooth_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:43.998879+00:00
-- url     : https://prove2.me/submissions/94cb0061-edc4-4194-8da8-4a36cff08c8a

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
theorem _root_.solution (hA : AdmUJ ε) (hG : GardingFin) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : SmoothOnH (Jm ε) fun g => σ g v := by
  obtain ⟨S, _, hvS, hS⟩ := hv
  obtain ⟨Y, _, -, hvY, hY⟩ := hA H σ hσ hirr S hS v hvS
  exact hG n ε H σ hσ Y hY v hvY
end CompanionTheory.D.gk.admitted
