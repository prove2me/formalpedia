-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.T_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:01.125099+00:00
-- url     : https://prove2.me/submissions/c6d4fd31-615a-4212-8bc6-b61f44db2f09

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_integral_mul_right_of_conj
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_apply_alt

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
theorem _root_.solution (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    (hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)) {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (h0 : 0 ≤ w) (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (u : H) :
    ∫ x, w x • ρ x (ρ k u) ∂μ = ρ k (∫ x, w x • ρ x u ∂μ) := by
  rw [apply_alt μ ρ hρ hmul hw hc,
    ← integral_mul_right_of_conj μ hw hc h0 h1 k hk (fun x => w (k⁻¹ * x) • ρ x u)]
  congr 1
  funext x
  rw [← mul_assoc, hk, hmul]
end CompanionTheory.D.gk.admitted.Gard
