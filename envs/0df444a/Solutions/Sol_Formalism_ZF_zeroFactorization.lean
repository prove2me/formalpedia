-- Prove2me | solution 1 for Formalism.ZF.zeroFactorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:55:26.808363+00:00
-- url     : https://prove2.me/submissions/7c524453-8429-4096-9af4-e4ec19e8f12f

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFactor
import Theorems.Thm_Formalism_ZF_exists_factorization_of_sum_order
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Set Filter Topology
noncomputable section
namespace Formalism.ZF
private theorem natCast_analyticOrderNatAt_of_ne_top {f : ℂ → ℂ} {z : ℂ}
    (h : analyticOrderAt f z ≠ ⊤) : ((analyticOrderNatAt f z : ℕ) : ℕ∞) = analyticOrderAt f z :=
  ENat.natCast_toNat h
end Formalism.ZF
end
end

set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : ZeroFactor := by
  intro f z₀ r R₁ hR₁ hR hf hf0
  have hr : 0 < r := hR₁.trans hR
  have hU : AnalyticOnNhd ℂ f (Metric.ball z₀ r) :=
    (hf.mono Metric.ball_subset_closedBall).analyticOnNhd Metric.isOpen_ball
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hpre : IsPreconnected (Metric.ball z₀ r) := (convex_ball z₀ r).isPreconnected
  have hnotzero : ∀ x ∈ Metric.ball z₀ r, ¬ (∀ᶠ w in 𝓝 x, f w = 0) := by
    intro x hx hev
    have hEq := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hx hev
    exact hf0 (hEq hz₀)
  have hisol : ∀ x ∈ Metric.ball z₀ r, ∀ᶠ w in 𝓝[≠] x, f w ≠ 0 := fun x hx =>
    ((hU x hx).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hnotzero x hx)
  have htop : ∀ x ∈ Metric.ball z₀ r, analyticOrderAt f x ≠ ⊤ := fun x hx h =>
    hnotzero x hx (analyticOrderAt_eq_top.mp h)
  have hSsub : Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0} ⊆ Metric.ball z₀ r :=
    fun x hx => Metric.closedBall_subset_ball hR hx.1
  have hScpt : IsCompact (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}) :=
    (isCompact_closedBall z₀ R₁).of_isClosed_subset
      ((hf.continuousOn.mono (Metric.closedBall_subset_closedBall hR.le)).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall isClosed_singleton)
      Set.inter_subset_left
  have hSdisc : DiscreteTopology (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0} : Set ℂ) := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    refine Filter.inf_principal_eq_bot.mpr ?_
    filter_upwards [hisol x (hSsub hx)] with w hw hwS
    exact hw hwS.2
  have hfin : (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}).Finite := by
    exact hScpt.finite ⟨hSdisc⟩
  have hmem : ∀ ρ : ℂ, ρ ∈ hfin.toFinset ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0) := by
    intro ρ
    rw [Set.Finite.mem_toFinset]
    rfl
  obtain ⟨h, hhd, hh0, hhf⟩ := exists_factorization_of_sum_order z₀ r R₁ hR _ f hfin.toFinset hf
    (fun ρ hρ => ((hmem ρ).mp hρ).1) (fun z hz hfz => (hmem z).mpr ⟨hz, hfz⟩)
    (fun ρ hρ => htop ρ (Metric.closedBall_subset_ball hR ((hmem ρ).mp hρ).1)) rfl
  refine ⟨hfin.toFinset, analyticOrderNatAt f, h, hmem, ?_, hhd, hh0, hhf⟩
  intro ρ hρ
  obtain ⟨hB, hfρ⟩ := (hmem ρ).mp hρ
  have hball : ρ ∈ Metric.ball z₀ r := Metric.closedBall_subset_ball hR hB
  have hne : analyticOrderAt f ρ ≠ 0 := fun h0 =>
    ((hU ρ hball).analyticOrderAt_eq_zero.mp h0) hfρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hne
  rw [← natCast_analyticOrderNatAt_of_ne_top (htop ρ hball)]
  simp [h0]
end Formalism.ZF
