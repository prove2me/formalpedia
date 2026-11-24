-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_cont_of_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:16.547838+00:00
-- url     : https://prove2.me/submissions/59e6895f-bf28-4919-b796-c917978d43cc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : G → (H →L[ℂ] H)}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [TopologicalSpace.SeparableSpace H] (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1)
    (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ) (x : H) :
    Continuous fun g => π g x := by
  have hd : Dense ((rrc_C π : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
    exact rrc_orth hmul hone hn hm
  have h1 : ∀ x, Tendsto (fun h => π h x) (𝓝 1) (𝓝 x) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s, hs, hxs⟩ := hd.exists_dist_lt x (by positivity : 0 < ε / 3)
    have hs' : Tendsto (fun h => π h s) (𝓝 1) (𝓝 s) := hs
    filter_upwards [(Metric.tendsto_nhds.1 hs') (ε / 3) (by positivity)] with h hh
    have a : dist (π h x) (π h s) = dist x s := by
      rw [dist_eq_norm, ← map_sub, hn, dist_eq_norm]
    calc dist (π h x) x ≤ dist (π h x) (π h s) + dist (π h s) s + dist s x := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
          rw [a, dist_comm s x]
          linarith
      _ = ε := by ring
  rw [continuous_iff_continuousAt]
  intro g₀
  have e : (fun g => π g x) = fun g => π g₀ (π (g₀⁻¹ * g) x) := by
    funext g
    rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel_left]
  have t : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using (continuous_const_mul g₀⁻¹).tendsto g₀
  have c := ((π g₀).continuous.tendsto x).comp ((h1 x).comp t)
  show Tendsto (fun g => π g x) (𝓝 g₀) (𝓝 (π g₀ x))
  rw [e]
  exact c
end Formalism.MainNotions.LeviCoordinates
