-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.exists_strictHenselian_absolutely_closed_local_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:44.429171+00:00
-- url     : https://prove2.me/submissions/460cbf70-756a-4c9e-ae72-9da9bcd008dd

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_integrable_w

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (hiso : ∀ x u, ‖ρ x u‖ = ‖u‖)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) :
    ∃ T : H →L[ℂ] H, ∀ u, T u = ∫ x, w x • ρ x u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ x, w x • ρ x u ∂μ
      map_add' := fun u v => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_w μ ρ hρ hw hc u) (integrable_w μ ρ hρ hw hc v)
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  refine ⟨L.mkContinuous (∫ x, ‖w x‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _
end CompanionTheory.D.gk.admitted.Gard
